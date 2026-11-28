use core::ffi::{c_char, c_int, c_void};
use core::mem::{offset_of, size_of};
use core::ptr::null_mut;

core::arch::global_asm!(
    ".hidden ghc_rust_pool_try_take",
    ".hidden ghc_rust_pool_release",
    ".hidden ghc_rust_pool_trim",
    ".hidden ghc_rust_pool_flush_taken",
);

type AllocFn = unsafe extern "C" fn() -> *mut c_void;
type FreeFn = unsafe extern "C" fn(*mut c_void);
const TAKE_EXHAUSTED: c_int = 0;
const TAKE_SUCCESS: c_int = 1;
const TAKE_ALLOC_FAILED: c_int = 2;

struct Entry {
    next: *mut Entry,
    thing: *mut c_void,
    should_free: bool,
}

/// Portable pool data. C owns the containing pool and its mutex and condition.
#[repr(C)]
pub(super) struct PoolState {
    max_size: u32,
    desired_size: u32,
    current_size: u32,
    alloc_fn: Option<AllocFn>,
    free_fn: Option<FreeFn>,
    available: *mut Entry,
    taken: *mut Entry,
}

const _: () = {
    assert!(size_of::<PoolState>() == 48);
    assert!(offset_of!(PoolState, max_size) == 0);
    assert!(offset_of!(PoolState, desired_size) == 4);
    assert!(offset_of!(PoolState, current_size) == 8);
    assert!(offset_of!(PoolState, alloc_fn) == 16);
    assert!(offset_of!(PoolState, free_fn) == 24);
    assert!(offset_of!(PoolState, available) == 32);
    assert!(offset_of!(PoolState, taken) == 40);
};

unsafe extern "C" {
    fn stgMallocBytes(size: usize, label: *const c_char) -> *mut c_void;
    fn stgFree(allocation: *mut c_void);
}

/// Return 0 when exhausted, 1 with a resource, or 2 on allocation failure.
/// The caller holds the pool mutex throughout this call.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_pool_try_take(
    state: *mut PoolState,
    thing_out: *mut *mut c_void,
) -> c_int {
    unsafe {
        let entry = if !(*state).available.is_null() {
            let entry = (*state).available;
            (*state).available = (*entry).next;
            entry
        } else if (*state).current_size < (*state).max_size {
            let entry = stgMallocBytes(size_of::<Entry>(), c"pool_take".as_ptr()).cast::<Entry>();
            let thing = (*state).alloc_fn.unwrap_unchecked()();
            if thing.is_null() {
                stgFree(entry.cast());
                return TAKE_ALLOC_FAILED;
            }
            entry.write(Entry {
                next: null_mut(),
                thing,
                should_free: false,
            });
            (*state).current_size += 1;
            entry
        } else {
            return TAKE_EXHAUSTED;
        };
        (*entry).next = (*state).taken;
        (*state).taken = entry;
        *thing_out = (*entry).thing;
        TAKE_SUCCESS
    }
}

/// Return 1 after releasing a claimed resource, or 0 if it was not claimed.
/// The caller holds the pool mutex throughout this call.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_pool_release(
    state: *mut PoolState,
    thing: *mut c_void,
) -> c_int {
    unsafe {
        let mut link = &raw mut (*state).taken;
        while !(*link).is_null() {
            let entry = *link;
            if (*entry).thing == thing {
                *link = (*entry).next;
                if (*state).current_size > (*state).desired_size || (*entry).should_free {
                    (*state).free_fn.unwrap_unchecked()((*entry).thing);
                    stgFree(entry.cast());
                    (*state).current_size -= 1;
                } else {
                    (*entry).next = (*state).available;
                    (*state).available = entry;
                }
                return 1;
            }
            link = &raw mut (*entry).next;
        }
        0
    }
}

/// Free idle resources until current_size is at most limit.
/// The caller holds the pool mutex throughout this call.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_pool_trim(state: *mut PoolState, limit: u32) {
    unsafe {
        while (*state).current_size > limit && !(*state).available.is_null() {
            let entry = (*state).available;
            (*state).free_fn.unwrap_unchecked()((*entry).thing);
            (*state).available = (*entry).next;
            stgFree(entry.cast());
            (*state).current_size -= 1;
        }
    }
}

/// Mark claimed resources for destruction when they are released.
/// The caller holds the pool mutex throughout this call.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_pool_flush_taken(state: *mut PoolState) {
    unsafe {
        let mut entry = (*state).taken;
        while !entry.is_null() {
            (*entry).should_free = true;
            entry = (*entry).next;
        }
    }
}
