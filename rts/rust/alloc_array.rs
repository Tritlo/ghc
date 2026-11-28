use core::ffi::c_void;
use core::mem::size_of;
use core::ptr::null_mut;
use core::sync::atomic::{AtomicPtr, AtomicUsize, Ordering};

core::arch::global_asm!(
    ".hidden ghc_rust_allocate_mut_array",
    ".hidden ghc_rust_allocate_small_mut_array",
    ".hidden ghc_rust_allocate_byte_array",
    ".hidden ghc_rust_allocate_pinned_byte_array",
    ".hidden ghc_rust_publish_shrink",
    ".hidden ghc_rust_shrink_small_array_active",
    ".hidden ghc_rust_visit_pointer_range",
);

unsafe extern "C" {
    static stg_MUT_ARR_PTRS_DIRTY_info: u8;
    static stg_SMALL_MUT_ARR_PTRS_DIRTY_info: u8;
    static stg_ARR_WORDS_info: u8;
    fn mutArrPtrsCards(count: usize) -> usize;
    fn allocateMightFail(cap: *mut c_void, words: usize) -> *mut c_void;
    fn allocatePinned(cap: *mut c_void, words: usize, align: usize, offset: usize) -> *mut c_void;
    fn updateRemembSetPushClosure_(reg: *mut c_void, closure: *mut c_void);
}

// See Note [shrink-array slop marker] in PrimOps.cmm and
// Note [Slop marker memory ordering] in ClosureMacros.h.
#[unsafe(no_mangle)]
unsafe extern "C" fn ghc_rust_publish_shrink(
    length: *mut usize,
    new_size: usize,
    slop: *mut usize,
    words: usize,
) {
    unsafe {
        if words == 1 {
            AtomicUsize::from_ptr(slop).store(0, Ordering::Relaxed);
        } else if words >= 2 {
            AtomicUsize::from_ptr(slop).store(usize::MAX, Ordering::Relaxed);
            AtomicUsize::from_ptr(slop.add(1)).store(words - 2, Ordering::Release);
        }
        AtomicUsize::from_ptr(length).store(new_size, Ordering::Relaxed);
    }
}

// Note [Pointer-array remembered-set visit]
// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
// See Note [Update remembered set] in rts/sm/NonMovingMark.c.
// Visit each removed pointer before the marker overwrites its slot.
// Visit old destination pointers before a copy overwrites their slots.
// The non-moving collector can update a slot with CAS, so load it atomically.
#[unsafe(no_mangle)]
unsafe extern "C" fn ghc_rust_visit_pointer_range(
    reg: *mut c_void,
    start: *mut *mut c_void,
    words: usize,
) {
    unsafe {
        for i in 0..words {
            let closure = AtomicPtr::from_ptr(start.add(i)).load(Ordering::Relaxed);
            updateRemembSetPushClosure_(reg, closure);
        }
    }
}

// See Note [Pointer-array remembered-set visit].
#[unsafe(no_mangle)]
unsafe extern "C" fn ghc_rust_shrink_small_array_active(
    reg: *mut c_void,
    length: *mut usize,
    new_size: usize,
) {
    unsafe {
        let old_size = AtomicUsize::from_ptr(length).load(Ordering::Relaxed);
        let payload = length.add(1).cast::<*mut c_void>();
        ghc_rust_visit_pointer_range(reg, payload.add(new_size), old_size - new_size);
        let final_size = AtomicUsize::from_ptr(length).load(Ordering::Relaxed);
        ghc_rust_publish_shrink(
            length,
            new_size,
            payload.add(new_size).cast::<usize>(),
            final_size - new_size,
        );
    }
}

type ArrayInstrumentation = Option<unsafe extern "C" fn(*mut c_void, *mut c_void, usize, usize)>;

// The RTS way determines the header size and optional instrumentation.
unsafe fn set_array_header(
    array: *mut c_void,
    info: *const u8,
    ccs: *mut c_void,
    header_words: usize,
    payload_words: usize,
    instrument: ArrayInstrumentation,
) {
    if let Some(instrument) = instrument {
        unsafe { instrument(array, ccs, header_words, payload_words) };
    }
    unsafe {
        AtomicPtr::from_ptr(array.cast::<*mut c_void>())
            .store(info.cast_mut().cast(), Ordering::Relaxed);
    }
}

unsafe fn allocate_byte_array(
    cap: *mut c_void,
    bytes: usize,
    alignment: Option<usize>,
    ccs: *mut c_void,
    header_bytes: usize,
    instrument: ArrayInstrumentation,
) -> *mut c_void {
    if bytes > usize::MAX - header_bytes {
        return null_mut();
    }

    let word = size_of::<usize>();
    let header_words = header_bytes / word;
    let payload_words = bytes.div_ceil(word);
    let words = header_words + payload_words;
    unsafe {
        let array = match alignment {
            Some(align) => allocatePinned(cap, words, align.max(word), header_bytes),
            None => allocateMightFail(cap, words),
        };
        if !array.is_null() {
            set_array_header(
                array,
                &raw const stg_ARR_WORDS_info,
                ccs,
                header_words,
                payload_words,
                instrument,
            );
            array
                .byte_add(header_bytes - word)
                .cast::<usize>()
                .write(bytes);
        }
        array
    }
}

#[unsafe(no_mangle)]
unsafe extern "C" fn ghc_rust_allocate_byte_array(
    cap: *mut c_void,
    bytes: usize,
    ccs: *mut c_void,
    header_bytes: usize,
    instrument: ArrayInstrumentation,
) -> *mut c_void {
    unsafe { allocate_byte_array(cap, bytes, None, ccs, header_bytes, instrument) }
}

#[unsafe(no_mangle)]
unsafe extern "C" fn ghc_rust_allocate_pinned_byte_array(
    cap: *mut c_void,
    bytes: usize,
    alignment: usize,
    ccs: *mut c_void,
    header_bytes: usize,
    instrument: ArrayInstrumentation,
) -> *mut c_void {
    unsafe { allocate_byte_array(cap, bytes, Some(alignment), ccs, header_bytes, instrument) }
}

/// Allocate a pointer array. Only the ordinary array has a card table.
unsafe fn allocate_pointer_array<const SMALL: bool>(
    cap: *mut c_void,
    count: usize,
    init: *mut c_void,
    ccs: *mut c_void,
    header_bytes: usize,
    instrument: ArrayInstrumentation,
) -> *mut c_void {
    let word = size_of::<usize>();
    if count > (usize::MAX - header_bytes) / word {
        return null_mut();
    }
    let card_bytes = if SMALL {
        0
    } else {
        unsafe { mutArrPtrsCards(count) }
    };
    let payload_words = count + card_bytes.div_ceil(word);
    let header_words = header_bytes / word;
    unsafe {
        let array = allocateMightFail(cap, header_words + payload_words);
        if array.is_null() {
            return null_mut();
        }
        let slots = array.byte_add(header_bytes).cast::<*mut c_void>();
        let metadata_end = slots.cast::<usize>();
        if SMALL {
            set_array_header(
                array,
                &raw const stg_SMALL_MUT_ARR_PTRS_DIRTY_info,
                ccs,
                header_words,
                payload_words,
                instrument,
            );
            metadata_end.sub(1).write(count);
        } else {
            set_array_header(
                array,
                &raw const stg_MUT_ARR_PTRS_DIRTY_info,
                ccs,
                header_words,
                payload_words,
                instrument,
            );
            metadata_end.sub(2).write(count);
            metadata_end.sub(1).write(payload_words);
        }
        if !init.is_null() {
            for index in 0..count {
                slots.add(index).write(init);
            }
        }
        if !SMALL {
            // The trailing alignment bytes of the card table stay untouched.
            slots.add(count).cast::<u8>().write_bytes(0, card_bytes);
        }
        array
    }
}

#[unsafe(no_mangle)]
unsafe extern "C" fn ghc_rust_allocate_mut_array(
    cap: *mut c_void,
    count: usize,
    init: *mut c_void,
    ccs: *mut c_void,
    header_bytes: usize,
    instrument: ArrayInstrumentation,
) -> *mut c_void {
    unsafe { allocate_pointer_array::<false>(cap, count, init, ccs, header_bytes, instrument) }
}

#[unsafe(no_mangle)]
unsafe extern "C" fn ghc_rust_allocate_small_mut_array(
    cap: *mut c_void,
    count: usize,
    init: *mut c_void,
    ccs: *mut c_void,
    header_bytes: usize,
    instrument: ArrayInstrumentation,
) -> *mut c_void {
    unsafe { allocate_pointer_array::<true>(cap, count, init, ccs, header_bytes, instrument) }
}
