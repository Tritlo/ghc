#![no_std]

use core::ffi::{CStr, c_char, c_void};
use core::ptr;

unsafe extern "C" {
    fn dirname(path: *mut c_char) -> *mut c_char;
    fn stgMallocBytes(size: usize, label: *const c_char) -> *mut c_void;
    fn stgFree(ptr: *mut c_void);
}

/// Copy a NUL-terminated POSIX path into an RTS allocation.
///
/// # Safety
///
/// `path` must point to a NUL-terminated string. The caller must free the
/// returned allocation with `stgFree`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn ghc_rust_pathdup(path: *const c_char) -> *mut c_char {
    let input = unsafe { CStr::from_ptr(path) }.to_bytes_with_nul();
    let result = unsafe { stgMallocBytes(input.len(), c"pathdup".as_ptr()) }.cast::<c_char>();
    unsafe { ptr::copy_nonoverlapping(input.as_ptr().cast(), result, input.len()) };
    result
}

/// Test whether a POSIX path ends with the given bytes.
///
/// # Safety
///
/// `base` and `suffix` must point to NUL-terminated strings.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn ghc_rust_ends_with_path(
    base: *const c_char,
    suffix: *const c_char,
) -> isize {
    let base = unsafe { CStr::from_ptr(base) }.to_bytes();
    let suffix = unsafe { CStr::from_ptr(suffix) }.to_bytes();
    if base.ends_with(suffix) { 1 } else { 0 }
}

/// Return the POSIX parent path with one trailing slash.
///
/// # Safety
///
/// `path` must point to a NUL-terminated string. The caller must free the
/// returned allocation with `stgFree`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn ghc_rust_pathdir(path: *const c_char) -> *mut c_char {
    let input = unsafe { CStr::from_ptr(path) }.to_bytes_with_nul();
    let copy = unsafe { stgMallocBytes(input.len(), c"pathdir(path)".as_ptr()) }.cast::<c_char>();
    unsafe { ptr::copy_nonoverlapping(input.as_ptr().cast(), copy, input.len()) };

    let dirname = unsafe { dirname(copy) };
    let parent = unsafe { CStr::from_ptr(dirname) }.to_bytes();
    let result =
        unsafe { stgMallocBytes(parent.len() + 2, c"pathdir(path)".as_ptr()) }.cast::<u8>();
    unsafe {
        ptr::copy_nonoverlapping(parent.as_ptr(), result, parent.len());
        *result.add(parent.len()) = b'/';
        *result.add(parent.len() + 1) = 0;
        stgFree(copy.cast());
    }
    result.cast()
}
