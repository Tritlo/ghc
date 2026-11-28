use core::ffi::c_void;
use core::mem::{offset_of, size_of};

core::arch::global_asm!(
    ".hidden ghc_rust_suspended_calls_insert",
    ".hidden ghc_rust_suspended_calls_remove",
    ".hidden ghc_rust_suspended_calls_visit",
    ".hidden ghc_rust_suspended_calls_find",
);

// C checks that InCall.prev and InCall.next are adjacent pointer fields.
#[repr(C)]
struct Links {
    prev: *mut c_void,
    next: *mut c_void,
}

const _: () = {
    assert!(offset_of!(Links, prev) == 0);
    assert!(offset_of!(Links, next) == size_of::<*mut c_void>());
    assert!(size_of::<Links>() == 2 * size_of::<*mut c_void>());
};

unsafe fn links(incall: *mut c_void, offset: usize) -> *mut Links {
    unsafe { incall.cast::<u8>().add(offset).cast::<Links>() }
}

unsafe fn suspended_tso_slot(incall: *mut c_void, offset: usize) -> *mut *mut c_void {
    unsafe { incall.cast::<u8>().add(offset).cast::<*mut c_void>() }
}

/// Add an in-call to the front of one capability's suspended list.
///
/// # Safety
///
/// C owns the list and has exclusive access while it holds the capability.
/// The in-call is not on a list. The checked C layout matches `Links`.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_suspended_calls_insert(
    head: *mut *mut c_void,
    count: *mut u32,
    incall: *mut c_void,
    links_offset: usize,
) {
    let fields = unsafe { links(incall, links_offset) };
    let first = unsafe { head.read() };
    unsafe {
        (&raw mut (*fields).next).write(first);
        (&raw mut (*fields).prev).write(core::ptr::null_mut());
        if !first.is_null() {
            (&raw mut (*links(first, links_offset)).prev).write(incall);
        }
        head.write(incall);
        count.write(count.read() + 1);
    }
}

/// Remove an in-call from one capability's suspended list.
///
/// # Safety
///
/// C owns the list and has exclusive access. The in-call belongs to the list.
/// The checked C layout matches `Links`.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_suspended_calls_remove(
    head: *mut *mut c_void,
    count: *mut u32,
    incall: *mut c_void,
    links_offset: usize,
) {
    let fields = unsafe { links(incall, links_offset) };
    let prev = unsafe { (&raw const (*fields).prev).read() };
    let next = unsafe { (&raw const (*fields).next).read() };
    unsafe {
        if prev.is_null() {
            head.write(next);
        } else {
            (&raw mut (*links(prev, links_offset)).next).write(next);
        }
        if !next.is_null() {
            (&raw mut (*links(next, links_offset)).prev).write(prev);
        }
        (&raw mut (*fields).prev).write(core::ptr::null_mut());
        (&raw mut (*fields).next).write(core::ptr::null_mut());
        count.write(count.read() - 1);
    }
}

/// Visit the live suspended TSO slots. The callback may replace each TSO.
///
/// # Safety
///
/// C stops list mutations during collection. Each in-call and slot remains
/// valid for this call. `tso_offset` names the actual writable pointer slot.
/// The callback does not change the list links.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_suspended_calls_visit(
    mut incall: *mut c_void,
    links_offset: usize,
    tso_offset: usize,
    evac: unsafe extern "C" fn(*mut c_void, *mut *mut c_void),
    user: *mut c_void,
) {
    while !incall.is_null() {
        let slot = unsafe { suspended_tso_slot(incall, tso_offset) };
        unsafe { evac(user, slot) };
        // Keep this read after evacuation, as in markCapability.
        incall = unsafe { (&raw const (*links(incall, links_offset)).next).read() };
    }
}

/// Find the first in-call whose suspended TSO matches the target.
///
/// # Safety
///
/// The caller owns the target capability. Its list and TSO slots are valid
/// throughout the search. The offsets come from the active C layout.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_suspended_calls_find(
    mut incall: *mut c_void,
    target: *mut c_void,
    links_offset: usize,
    tso_offset: usize,
) -> *mut c_void {
    while !incall.is_null() {
        if unsafe { suspended_tso_slot(incall, tso_offset).read() } == target {
            break;
        }
        incall = unsafe { (*links(incall, links_offset)).next };
    }
    incall
}
