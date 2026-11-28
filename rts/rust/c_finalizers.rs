use core::ffi::c_void;
use core::sync::atomic::{AtomicPtr, Ordering};

core::arch::global_asm!(
    ".hidden ghc_rust_run_c_finalizers",
    ".hidden ghc_rust_run_all_c_finalizers",
);

unsafe extern "C" {
    static stg_NO_FINALIZER_closure: u8;
    static stg_DEAD_WEAK_info: u8;
}

// See Note [Weak finalizer traversal] in Weak.c.
#[repr(C)]
union Callback {
    plain: unsafe extern "C" fn(*mut c_void),
    with_env: unsafe extern "C" fn(*mut c_void, *mut c_void),
}

#[repr(C)]
struct Finalizer {
    link: *mut u8,
    callback: Callback,
    ptr: *mut c_void,
    env: *mut c_void,
    has_env: usize,
}

#[unsafe(no_mangle)]
unsafe extern "C" fn ghc_rust_run_c_finalizers(mut head: *mut u8, payload_offset: usize) {
    while head.cast_const() != &raw const stg_NO_FINALIZER_closure {
        unsafe {
            let node = head.add(payload_offset).cast::<Finalizer>();
            if (*node).has_env != 0 {
                ((*node).callback.with_env)((*node).env, (*node).ptr);
            } else {
                ((*node).callback.plain)((*node).ptr);
            }
            head = (*node).link;
        }
    }
}

unsafe fn run_weak_callbacks(weak: *mut u8, callbacks_offset: usize, payload_offset: usize) {
    unsafe {
        let callbacks = weak.add(callbacks_offset).cast::<*mut u8>().read();
        ghc_rust_run_c_finalizers(callbacks, payload_offset);
    }
}

#[unsafe(no_mangle)]
unsafe extern "C" fn ghc_rust_run_all_c_finalizers(
    mut weak: *mut u8,
    running: *mut bool,
    callbacks_offset: usize,
    link_offset: usize,
    payload_offset: usize,
) {
    unsafe {
        if !running.is_null() {
            running.write(true);
        }
        while !weak.is_null() {
            let info = AtomicPtr::from_ptr(weak.cast::<*mut u8>()).load(Ordering::Acquire);
            if info.cast_const() != &raw const stg_DEAD_WEAK_info {
                run_weak_callbacks(weak, callbacks_offset, payload_offset);
            }
            weak = weak.add(link_offset).cast::<*mut u8>().read();
        }
        if !running.is_null() {
            running.write(false);
        }
    }
}

// The queue owner holds its drain lock. GC has marked these entries DEAD_WEAK.
pub(super) unsafe fn drain_c_finalizers(
    cursor: *mut *mut u8,
    limit: usize,
    callbacks_offset: usize,
    link_offset: usize,
    payload_offset: usize,
) -> usize {
    unsafe {
        let mut weak = cursor.read();
        let mut count = 0;
        while !weak.is_null() && count < limit {
            run_weak_callbacks(weak, callbacks_offset, payload_offset);
            weak = weak.add(link_offset).cast::<*mut u8>().read();
            count += 1;
        }
        cursor.write(weak);
        count
    }
}
