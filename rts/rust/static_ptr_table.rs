use core::{
    ffi::{c_char, c_void},
    mem::size_of,
};

core::arch::global_asm!(
    ".hidden ghc_rust_spt_new_entry",
    ".hidden ghc_rust_spt_free_entry",
);

unsafe extern "C" {
    fn stgMallocBytes(size: usize, label: *const c_char) -> *mut c_void;
    fn stgFree(allocation: *mut c_void);
    fn getStablePtr(closure: *mut c_void) -> *mut c_void;
    fn freeStablePtr(root: *mut c_void);
}

/// Allocate a cell, then create its stable pointer root.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_spt_new_entry(closure: *mut c_void) -> *mut *mut c_void {
    unsafe {
        let entry = stgMallocBytes(size_of::<*mut c_void>(), c"hs_spt_insert: entry".as_ptr())
            .cast::<*mut c_void>();
        entry.write(getStablePtr(closure));
        entry
    }
}

/// Release the root before freeing its cell.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_spt_free_entry(entry: *mut c_void) {
    unsafe {
        freeStablePtr(entry.cast::<*mut c_void>().read());
        stgFree(entry);
    }
}
