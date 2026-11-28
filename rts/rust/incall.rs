use core::ffi::{c_char, c_int, c_void};
use core::mem::{align_of, offset_of, size_of};
use core::ptr::null_mut;

core::arch::global_asm!(
    ".hidden ghc_rust_incall_push",
    ".hidden ghc_rust_incall_pop",
    ".hidden ghc_rust_incall_free",
);

// See Note [In-call frame ownership] in rts/Task.c.
#[repr(C)]
pub(super) struct InCall {
    tso: *mut c_void,
    suspended_tso: *mut c_void,
    suspended_cap: *mut c_void,
    rstat: c_int,
    ret: *mut *mut c_void,
    task: *mut c_void,
    prev_stack: *mut InCall,
    prev: *mut InCall,
    next: *mut InCall,
}

const _: () = {
    assert!(size_of::<InCall>() == 72 && align_of::<InCall>() == 8);
    assert!(offset_of!(InCall, tso) == 0);
    assert!(offset_of!(InCall, suspended_tso) == 8);
    assert!(offset_of!(InCall, suspended_cap) == 16);
    assert!(offset_of!(InCall, rstat) == 24);
    assert!(offset_of!(InCall, ret) == 32);
    assert!(offset_of!(InCall, task) == 40);
    assert!(offset_of!(InCall, prev_stack) == 48);
    assert!(offset_of!(InCall, prev) == 56);
    assert!(offset_of!(InCall, next) == 64);
};

unsafe extern "C" {
    fn stgMallocBytes(size: usize, label: *const c_char) -> *mut c_void;
    fn stgFree(ptr: *mut c_void);
}

/// Push a newly initialized frame onto the owning task's stack.
///
/// # Safety
///
/// The three field pointers refer to the same task. Its stack and cache are
/// disjoint, and the caller has exclusive access to both.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_incall_push(
    task: *mut c_void,
    active: *mut *mut InCall,
    spares: *mut *mut InCall,
    spare_count: *mut u32,
) {
    unsafe {
        let mut frame = *spares;
        if frame.is_null() {
            frame = stgMallocBytes(size_of::<InCall>(), c"newInCall".as_ptr()).cast();
        } else {
            *spares = (*frame).next;
            *spare_count -= 1;
        }
        (*frame).tso = null_mut();
        (*frame).suspended_tso = null_mut();
        (*frame).suspended_cap = null_mut();
        (*frame).rstat = 0; // NoStatus
        (*frame).ret = null_mut();
        (*frame).task = task;
        (*frame).prev_stack = *active;
        (*frame).prev = null_mut();
        (*frame).next = null_mut();
        *active = frame;
    }
}

/// Pop the active frame. Cache it if the task has room for another spare.
///
/// # Safety
///
/// The caller has exclusive access to the nonempty stack and its spare cache.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_incall_pop(
    active: *mut *mut InCall,
    spares: *mut *mut InCall,
    spare_count: *mut u32,
    limit: u32,
) {
    unsafe {
        let frame = *active;
        (*frame).tso = null_mut();
        *active = (*frame).prev_stack;
        if *spare_count >= limit {
            stgFree(frame.cast());
        } else {
            (*frame).next = *spares;
            *spares = frame;
            *spare_count += 1;
        }
    }
}

/// Free active frames in stack order, then spare frames in list order.
///
/// # Safety
///
/// The task owns both chains and no caller can access the frames after this call.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_incall_free(
    mut active: *mut InCall,
    mut spares: *mut InCall,
) {
    unsafe {
        while !active.is_null() {
            let next = (*active).prev_stack;
            stgFree(active.cast());
            active = next;
        }
        while !spares.is_null() {
            let next = (*spares).next;
            stgFree(spares.cast());
            spares = next;
        }
    }
}
