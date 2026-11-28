#![no_std]

use core::mem::size_of;
use core::sync::atomic::{AtomicPtr, Ordering};

include!(env!("CLOSURE_SIZE_LAYOUT_RS"));
mod compact;
mod nonmoving;

unsafe extern "C" {
    #[link_name = "closure_sizeW_"]
    fn interposable_closure_size(p: *const u8, info: *const u8) -> u32;
}

#[inline]
unsafe fn closure_words(closure: *const u8) -> u32 {
    unsafe {
        let raw = AtomicPtr::from_ptr(
            closure
                .add(CLOSURE_INFO_OFFSET)
                .cast_mut()
                .cast::<*mut u8>(),
        )
        .load(Ordering::Relaxed);
        interposable_closure_size(closure, raw.wrapping_sub(INFO_TABLE_BIAS))
    }
}

#[inline]
unsafe fn read_u32(base: *const u8, offset: usize) -> u32 {
    unsafe { base.add(offset).cast::<u32>().read() }
}

#[inline]
unsafe fn read_word(base: *const u8, offset: usize) -> usize {
    unsafe { base.add(offset).cast::<usize>().read() }
}

#[inline]
unsafe fn payload_words(info: *const u8, header: u32) -> u32 {
    unsafe {
        header
            .wrapping_add(read_u32(info, INFO_PTRS_OFFSET))
            .wrapping_add(read_u32(info, INFO_NPTRS_OFFSET))
    }
}

/// Return the size of a heap closure in words.
///
/// The caller supplies the untagged closure and its decoded info table.
/// See Note [Closure size build constants] in ClosureSizeConstants.c.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn closure_sizeW_(p: *const u8, info: *const u8) -> u32 {
    unsafe {
        let kind = read_u32(info, INFO_TYPE_OFFSET);
        match kind {
            TAG_THUNK_0_1 | TAG_THUNK_1_0 => THUNK_WORDS + 1,
            TAG_FUN_0_1 | TAG_CONSTR_0_1 | TAG_FUN_1_0 | TAG_CONSTR_1_0 => HEADER_WORDS + 1,
            TAG_THUNK_0_2 | TAG_THUNK_1_1 | TAG_THUNK_2_0 => THUNK_WORDS + 2,
            TAG_FUN_0_2 | TAG_CONSTR_0_2 | TAG_FUN_1_1 | TAG_CONSTR_1_1 | TAG_FUN_2_0
            | TAG_CONSTR_2_0 => HEADER_WORDS + 2,
            TAG_THUNK => payload_words(info, THUNK_WORDS),
            TAG_THUNK_SELECTOR => SELECTOR_WORDS,
            TAG_AP_STACK => AP_STACK_WORDS.wrapping_add(read_word(p, AP_STACK_SIZE_OFFSET) as u32),
            TAG_AP => AP_WORDS.wrapping_add(read_u32(p, AP_N_ARGS_OFFSET)),
            TAG_PAP => PAP_WORDS.wrapping_add(read_u32(p, PAP_N_ARGS_OFFSET)),
            TAG_IND => IND_WORDS,
            TAG_ARR_WORDS => {
                let bytes = read_word(p, ARR_BYTES_OFFSET);
                let word_bytes = size_of::<usize>();
                ARR_WORDS.wrapping_add((bytes.wrapping_add(word_bytes - 1) / word_bytes) as u32)
            }
            TAG_MUT_ARR_PTRS_CLEAN
            | TAG_MUT_ARR_PTRS_DIRTY
            | TAG_MUT_ARR_PTRS_FROZEN_CLEAN
            | TAG_MUT_ARR_PTRS_FROZEN_DIRTY => {
                MUT_ARR_WORDS.wrapping_add(read_word(p, MUT_ARR_SIZE_OFFSET) as u32)
            }
            TAG_SMALL_MUT_ARR_PTRS_CLEAN
            | TAG_SMALL_MUT_ARR_PTRS_DIRTY
            | TAG_SMALL_MUT_ARR_PTRS_FROZEN_CLEAN
            | TAG_SMALL_MUT_ARR_PTRS_FROZEN_DIRTY => {
                SMALL_ARR_WORDS.wrapping_add(read_word(p, SMALL_ARR_PTRS_OFFSET) as u32)
            }
            TAG_TSO => TSO_WORDS,
            TAG_STACK => STACK_WORDS.wrapping_add(read_u32(p, STACK_SIZE_OFFSET)),
            TAG_BCO => read_u32(p, BCO_SIZE_OFFSET),
            TAG_TREC_CHUNK => TREC_CHUNK_WORDS,
            TAG_CONTINUATION => {
                CONTINUATION_WORDS.wrapping_add(read_word(p, CONTINUATION_SIZE_OFFSET) as u32)
            }
            _ => payload_words(info, CLOSURE_WORDS),
        }
    }
}
