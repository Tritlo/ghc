use core::ffi::{c_char, c_int, c_void};
use core::mem::{align_of, size_of};
use core::ptr::copy_nonoverlapping;
use core::sync::atomic::{AtomicPtr, AtomicUsize, Ordering};

const _: () = {
    assert!(size_of::<AtomicPtr<c_void>>() == size_of::<*mut c_void>());
    assert!(align_of::<AtomicPtr<c_void>>() == align_of::<*mut c_void>());
    assert!(size_of::<AtomicUsize>() == size_of::<usize>());
    assert!(align_of::<AtomicUsize>() == align_of::<usize>());
};

core::arch::global_asm!(
    ".hidden ghc_rust_make_thread_label",
    ".hidden ghc_rust_label_thread",
);

unsafe extern "C" {
    fn strlen(text: *const c_char) -> usize;
    fn allocateArrBytes(cap: *mut c_void, bytes: usize, ccs: *mut c_void) -> *mut c_void;
    fn updateRemembSetPushClosure(cap: *mut c_void, label: *mut c_void);
    fn recordClosureMutated(cap: *mut c_void, tso: *mut c_void);
    static mut nonmoving_write_barrier_enabled: usize;
}

/// Allocate and initialize a label from a NUL-terminated C string.
/// C supplies the payload offset and the current cost centre stack.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_make_thread_label(
    cap: *mut c_void,
    text: *const c_char,
    ccs: *mut c_void,
    payload_offset: usize,
) -> *mut c_void {
    unsafe {
        let len = strlen(text);
        let array = allocateArrBytes(cap, len, ccs);
        if !array.is_null() {
            copy_nonoverlapping(
                text.cast::<u8>(),
                array.byte_add(payload_offset).cast(),
                len,
            );
        }
        array
    }
}

/// Record the old label for the collector and publish the new label.
/// C owns the TSO layout and emits the event after this call returns.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_label_thread(
    slot: *mut *mut c_void,
    cap: *mut c_void,
    tso: *mut c_void,
    label: *mut c_void,
    barrier_possible: c_int,
) {
    unsafe {
        let slot = AtomicPtr::from_ptr(slot);
        let old_label = slot.load(Ordering::Acquire);
        if barrier_possible != 0 && !old_label.is_null() {
            let barrier_enabled = AtomicUsize::from_ptr(&raw mut nonmoving_write_barrier_enabled)
                .load(Ordering::Relaxed);
            if barrier_enabled != 0 {
                updateRemembSetPushClosure(cap, old_label);
            }
        }
        recordClosureMutated(cap, tso);
        slot.store(label, Ordering::Release);
    }
}
