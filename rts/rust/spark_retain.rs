#![no_std]

use core::ffi::c_void;

type RetainSpark = unsafe extern "C" fn(*mut c_void, *mut c_void) -> *mut c_void;

/// Retain deque entries in circular order, starting the output at the old
/// bottom. Return the number of retained slots.
///
/// # Safety
///
/// The caller must exclude all other access to the deque's slots throughout
/// the call, including from the callback. Slots must have space for mask + 1
/// pointers, where mask + 1 is a power of two. Top must be normalized to the
/// mask, count must be at most mask + 1, and the count live slots beginning at
/// top must be initialized. The callback receives each pointer once and may
/// return an unchanged or replacement pointer, or null to remove it.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn ghc_rust_retain_spark_slots(
    slots: *mut *mut c_void,
    top: usize,
    count: usize,
    mask: usize,
    retain: RetainSpark,
    state: *mut c_void,
) -> usize {
    let output = top + count;
    let mut retained = 0;
    for offset in 0..count {
        let index = (top + offset) & mask;
        let spark = unsafe { slots.add(index).read() };
        let keep = unsafe { retain(state, spark) };
        if !keep.is_null() {
            let destination = (output + retained) & mask;
            unsafe { slots.add(destination).write(keep) };
            retained += 1;
        }
    }
    retained
}
