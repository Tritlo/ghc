use core::ffi::c_void;
use core::ptr::null_mut;
use core::sync::atomic::{AtomicPtr, Ordering};

core::arch::global_asm!(
    ".hidden ghc_rust_top_handler_init",
    ".hidden ghc_rust_top_handler_set",
    ".hidden ghc_rust_top_handler_weak",
    ".hidden ghc_rust_top_handler_thread",
    ".hidden ghc_rust_top_handler_exit",
);

unsafe extern "C" {
    fn getStablePtr(value: *mut c_void) -> *mut c_void;
    fn deRefStablePtr(handle: *mut c_void) -> *mut c_void;
    fn freeStablePtr(handle: *mut c_void);
    static stg_WEAK_info: u8;
    static stg_DEAD_WEAK_info: u8;
}

// See Note [Top handler stable pointer] in TopHandler.c.
static mut TOP_HANDLER: *mut c_void = null_mut();

#[unsafe(no_mangle)]
unsafe extern "C" fn ghc_rust_top_handler_init() {
    unsafe { TOP_HANDLER = null_mut() }
}

#[unsafe(no_mangle)]
unsafe extern "C" fn ghc_rust_top_handler_set(weak: *mut c_void) {
    unsafe {
        if !TOP_HANDLER.is_null() {
            freeStablePtr(TOP_HANDLER);
        }
        TOP_HANDLER = getStablePtr(weak);
    }
}

#[unsafe(no_mangle)]
unsafe extern "C" fn ghc_rust_top_handler_weak() -> *mut c_void {
    unsafe { deRefStablePtr(TOP_HANDLER) }
}

#[unsafe(no_mangle)]
unsafe extern "C" fn ghc_rust_top_handler_thread(
    weak: *mut c_void,
    key_offset: usize,
    check_key: Option<unsafe extern "C" fn(*mut c_void)>,
    invalid_weak: unsafe extern "C" fn(*mut c_void, *mut u8),
) -> *mut c_void {
    if weak.is_null() {
        return null_mut();
    }
    unsafe {
        let info = AtomicPtr::from_ptr(weak.cast::<*mut u8>()).load(Ordering::Acquire);
        if info.cast_const() == &raw const stg_WEAK_info {
            let key = weak.byte_add(key_offset).cast::<*mut c_void>().read();
            if let Some(check) = check_key {
                check(key);
            }
            return key;
        }
        if info.cast_const() != &raw const stg_DEAD_WEAK_info {
            invalid_weak(weak, info);
        }
        null_mut()
    }
}

#[unsafe(no_mangle)]
unsafe extern "C" fn ghc_rust_top_handler_exit() {
    unsafe {
        freeStablePtr(TOP_HANDLER);
        TOP_HANDLER = null_mut();
    }
}
