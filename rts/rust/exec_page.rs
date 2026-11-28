use core::ffi::{c_char, c_int, c_void};

const MEM_READ_EXECUTE: c_int = 4;

unsafe extern "C" {
    fn getPageSize() -> usize;
    fn mmapAnon(bytes: usize) -> *mut c_void;
    fn mprotectForLinker(start: *mut c_void, len: usize, mode: c_int);
    fn flushExec(len: usize, exec_addr: *mut c_void);
    fn munmapForLinker(addr: *mut c_void, bytes: usize, caller: *const c_char);
}

#[unsafe(no_mangle)]
pub extern "C" fn allocateExecPage() -> *mut c_void {
    unsafe { mmapAnon(getPageSize()) }
}

/// Make an allocated page executable.
///
/// # Safety
///
/// `page` must come from `allocateExecPage` and remain allocated.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn freezeExecPage(page: *mut c_void) {
    unsafe {
        mprotectForLinker(page, getPageSize(), MEM_READ_EXECUTE);
        flushExec(getPageSize(), page);
    }
}

/// Release an allocated page.
///
/// # Safety
///
/// `page` must come from `allocateExecPage` and remain allocated.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn freeExecPage(page: *mut c_void) {
    unsafe { munmapForLinker(page, getPageSize(), c"freeExecPage".as_ptr()) }
}
