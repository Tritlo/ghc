use super::{
    BQ_BH, BQ_LINK, BQ_OWNER, BQ_QUEUE, CLOSURE_INFO, Closure, INFO_PTRS, INFO_TYPE, MUT_VAR,
    MUTLIST_ASSERTS, MUTLIST_BD_FREE, MUTLIST_BD_GEN, MUTLIST_BD_LINK, MUTLIST_BD_START,
    MUTLIST_BDESCR_SHIFT, MUTLIST_BLOCK_SHIFT, MUTLIST_BLOCK_SIZE_W, MUTLIST_INFO_BIAS,
    MUTLIST_INLINE_CLEAN, MUTLIST_MBLOCK_SHIFT, MVAR_HEAD, MVAR_TAIL, MVAR_VALUE, PAYLOAD,
    SELECTEE, TAG_ARR_WORDS, TAG_BLOCKING_QUEUE, TAG_CONSTR, TAG_CONSTR_0_1, TAG_CONSTR_0_2,
    TAG_CONSTR_1_0, TAG_CONSTR_1_1, TAG_CONSTR_2_0, TAG_CONSTR_NOCAF, TAG_FUN, TAG_FUN_0_1,
    TAG_FUN_0_2, TAG_FUN_1_0, TAG_FUN_1_1, TAG_FUN_2_0, TAG_MUT_VAR_CLEAN, TAG_MUT_VAR_DIRTY,
    TAG_MVAR_CLEAN, TAG_MVAR_DIRTY, TAG_PRIM, TAG_THUNK, TAG_THUNK_0_1, TAG_THUNK_0_2,
    TAG_THUNK_1_0, TAG_THUNK_1_1, TAG_THUNK_2_0, TAG_THUNK_SELECTOR, TAG_TVAR, TAG_WEAK,
    THUNK_PAYLOAD, TVAR_CURRENT, TVAR_FIRST_WATCH,
};
use core::{
    mem::size_of,
    ptr,
    sync::atomic::{AtomicPtr, Ordering},
};

// See Note [Nonmoving mutable-list sweep] in NonMovingSweep.c.
struct MutListContext {
    heap_begin: usize,
    heap_end: usize,
    oldest: *const u8,
}

unsafe extern "C" {
    fn ghc_c_mut_list_alive_checked(closure: Closure) -> bool;
    fn ghc_c_record_mutable(closure: Closure, cap: *mut u8);
    fn nonmovingIsAlive(closure: Closure) -> bool;
    fn ghc_c_mut_list_pointer_clean(ptr: *mut u8) -> bool;
    static stg_MVAR_CLEAN_info: u8;
    static stg_MVAR_DIRTY_info: u8;
    static stg_TVAR_CLEAN_info: u8;
    static stg_TVAR_DIRTY_info: u8;
    static stg_MUT_VAR_CLEAN_info: u8;
    static stg_MUT_VAR_DIRTY_info: u8;
    static stg_BLOCKING_QUEUE_CLEAN_info: u8;
    static stg_BLOCKING_QUEUE_DIRTY_info: u8;
}

#[inline]
unsafe fn pointer(c: *mut u8, offset: usize) -> *mut u8 {
    unsafe { c.add(offset).cast::<*mut u8>().read() }
}

#[inline]
unsafe fn pointer_clean(value: *mut u8, context: &MutListContext) -> bool {
    if MUTLIST_INLINE_CLEAN != 0 {
        unsafe {
            let address = value.addr();
            let begin = context.heap_begin;
            let end = context.heap_end;
            if address < begin || address >= end {
                return true;
            }
            let mblock_mask = (1usize << MUTLIST_MBLOCK_SHIFT) - 1;
            let block_mask = (1usize << MUTLIST_BLOCK_SHIFT) - 1;
            let descriptor_address = ((address & mblock_mask & !block_mask)
                >> (MUTLIST_BLOCK_SHIFT - MUTLIST_BDESCR_SHIFT))
                | (address & !mblock_mask);
            let descriptor = ptr::with_exposed_provenance::<u8>(descriptor_address);
            descriptor.add(MUTLIST_BD_GEN).cast::<*const u8>().read() == context.oldest
        }
    } else {
        unsafe { ghc_c_mut_list_pointer_clean(value) }
    }
}

#[inline]
unsafe fn fields_clean(c: *mut u8, offsets: &[usize], context: &MutListContext) -> bool {
    for &offset in offsets {
        if !unsafe { pointer_clean(pointer(c, offset), context) } {
            return false;
        }
    }
    true
}

#[inline]
unsafe fn payload_clean(
    c: *mut u8,
    info: *const u8,
    offset: usize,
    context: &MutListContext,
) -> bool {
    let count = unsafe { info.add(INFO_PTRS).cast::<u32>().read() as usize };
    for index in 0..count {
        let ptr = unsafe { c.add(offset).cast::<*mut u8>().add(index).read() };
        if !unsafe { pointer_clean(ptr, context) } {
            return false;
        }
    }
    true
}

#[inline]
unsafe fn set_info(c: *mut u8, info: *const u8) {
    unsafe { c.add(CLOSURE_INFO).cast::<*const u8>().write(info) }
}

/// Classify one live mutable-list closure in the order used by the native sweep.
#[inline(always)]
unsafe fn classify(c: *mut u8, info: *const u8, context: &MutListContext) -> bool {
    unsafe {
        let kind = info.add(INFO_TYPE).cast::<u32>().read();
        match kind {
            TAG_MVAR_CLEAN | TAG_MVAR_DIRTY => {
                let clean = fields_clean(c, &[MVAR_HEAD, MVAR_TAIL, MVAR_VALUE], context);
                set_info(
                    c,
                    if clean {
                        ptr::addr_of!(stg_MVAR_CLEAN_info)
                    } else {
                        ptr::addr_of!(stg_MVAR_DIRTY_info)
                    },
                );
                clean
            }
            TAG_TVAR => {
                let clean = fields_clean(c, &[TVAR_CURRENT, TVAR_FIRST_WATCH], context);
                set_info(
                    c,
                    if clean {
                        ptr::addr_of!(stg_TVAR_CLEAN_info)
                    } else {
                        ptr::addr_of!(stg_TVAR_DIRTY_info)
                    },
                );
                clean
            }
            TAG_THUNK | TAG_THUNK_1_0 | TAG_THUNK_0_1 | TAG_THUNK_1_1 | TAG_THUNK_0_2
            | TAG_THUNK_2_0 => payload_clean(c, info, THUNK_PAYLOAD, context),
            TAG_FUN | TAG_FUN_1_0 | TAG_FUN_0_1 | TAG_FUN_1_1 | TAG_FUN_0_2 | TAG_FUN_2_0
            | TAG_CONSTR | TAG_CONSTR_NOCAF | TAG_CONSTR_1_0 | TAG_CONSTR_0_1 | TAG_CONSTR_1_1
            | TAG_CONSTR_0_2 | TAG_CONSTR_2_0 | TAG_PRIM => {
                payload_clean(c, info, PAYLOAD, context)
            }
            TAG_WEAK => false,
            TAG_MUT_VAR_CLEAN | TAG_MUT_VAR_DIRTY => {
                let clean = fields_clean(c, &[MUT_VAR], context);
                set_info(
                    c,
                    if clean {
                        ptr::addr_of!(stg_MUT_VAR_CLEAN_info)
                    } else {
                        ptr::addr_of!(stg_MUT_VAR_DIRTY_info)
                    },
                );
                clean
            }
            TAG_BLOCKING_QUEUE => {
                let clean = fields_clean(c, &[BQ_BH, BQ_OWNER, BQ_QUEUE, BQ_LINK], context);
                set_info(
                    c,
                    if clean {
                        ptr::addr_of!(stg_BLOCKING_QUEUE_CLEAN_info)
                    } else {
                        ptr::addr_of!(stg_BLOCKING_QUEUE_DIRTY_info)
                    },
                );
                clean
            }
            TAG_THUNK_SELECTOR => fields_clean(c, &[SELECTEE], context),
            TAG_ARR_WORDS => true,
            _ => false,
        }
    }
}

core::arch::global_asm!(".hidden ghc_rust_sweep_mut_list_blocks");

#[inline]
unsafe fn record_mutable(closure: Closure, cap: *mut u8, active_list: *mut *mut u8) {
    unsafe {
        let bd = active_list.read();
        let free_field = bd.add(MUTLIST_BD_FREE).cast::<*mut u8>();
        let free = AtomicPtr::from_ptr(free_field).load(Ordering::Relaxed);
        let start = bd.add(MUTLIST_BD_START).cast::<*mut u8>().read();
        let end = start.add(MUTLIST_BLOCK_SIZE_W * size_of::<usize>());
        if free.addr() >= end.addr() {
            ghc_c_record_mutable(closure, cap);
        } else {
            AtomicPtr::from_ptr(free.cast::<*mut u8>()).store(closure, Ordering::Relaxed);
            AtomicPtr::from_ptr(free_field).store(free.add(size_of::<usize>()), Ordering::Relaxed);
        }
    }
}

/// Scan the old mutable-list blocks in their native order.
/// C replaces the capability list before this call and frees old blocks after it.
#[unsafe(no_mangle)]
unsafe extern "C" fn ghc_rust_sweep_mut_list_blocks(
    mut bd: *mut u8,
    cap: *mut u8,
    heap_begin: usize,
    heap_end: usize,
    oldest: *const u8,
    active_list: *mut *mut u8,
) {
    unsafe {
        let context = MutListContext {
            heap_begin,
            heap_end,
            oldest,
        };
        while !bd.is_null() {
            let mut slot = bd.add(MUTLIST_BD_START).cast::<*mut Closure>().read();
            let end = bd.add(MUTLIST_BD_FREE).cast::<*mut Closure>().read();
            while slot.addr() < end.addr() {
                let closure = slot.read();
                let alive = if MUTLIST_ASSERTS != 0 {
                    ghc_c_mut_list_alive_checked(closure)
                } else {
                    nonmovingIsAlive(closure)
                };
                if alive {
                    let raw_info = AtomicPtr::from_ptr(closure.add(CLOSURE_INFO).cast::<*mut u8>())
                        .load(Ordering::Relaxed);
                    let info = raw_info.wrapping_sub(MUTLIST_INFO_BIAS);
                    if !classify(closure, info, &context) {
                        record_mutable(closure, cap, active_list);
                    }
                }
                slot = slot.add(1);
            }
            bd = bd.add(MUTLIST_BD_LINK).cast::<*mut u8>().read();
        }
    }
}
