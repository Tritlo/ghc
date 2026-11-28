#![no_std]

use core::ffi::{c_int, c_short, c_void};

// Match struct pollfd. Poll.c checks the layout for the Rust-enabled target.
#[repr(C)]
pub struct PollFd {
    fd: c_int,
    events: c_short,
    revents: c_short,
}

unsafe extern "C" {
    fn ghc_rust_poll_complete_slot(iomgr: *mut c_void, index: c_int, revents: c_short);
}

/// Scan the dense poll slots and complete ready operations in slot order.
///
/// # Safety
///
/// The caller owns the poll manager and its count initialized slots
/// exclusively. The slot count and number ready satisfy 0 <= ready <= count.
/// The C completion function removes one entry by swapping the last slot into
/// its place. It does not resize or replace the slot array.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn ghc_rust_poll_process_ready(
    iomgr: *mut c_void,
    slots: *mut PollFd,
    count: c_int,
    ready: c_int,
) -> c_int {
    let mut index = 0;
    let mut end = count;
    while index < end && count - end < ready {
        let revents = unsafe { (&raw const (*slots.add(index as usize)).revents).read() };
        if revents == 0 {
            index += 1;
        } else {
            // C moves the last slot into this index before notifying the TSO.
            unsafe { ghc_rust_poll_complete_slot(iomgr, index, revents) };
            end -= 1;
        }
    }
    count - end
}
