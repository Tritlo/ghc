#![no_std]

use core::ffi::{c_char, c_int};

unsafe extern "C" {
    static mut environ: *mut *mut c_char;
}

/// Return the borrowed POSIX environment vector and its entry count.
///
/// # Safety
///
/// Both output pointers must be valid. The caller must not change the
/// environment while this function reads the vector.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn ghc_rust_get_prog_envv(
    out_envc: *mut c_int,
    out_envv: *mut *mut *mut c_char,
) {
    let envv = unsafe { environ };
    let mut envc: c_int = 0;
    while !unsafe { *envv.add(envc as usize) }.is_null() {
        envc += 1;
    }
    unsafe {
        *out_envc = envc;
        *out_envv = envv;
    }
}
