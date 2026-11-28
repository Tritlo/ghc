#![no_std]

use core::ffi::{c_char, c_void};
use core::mem::{align_of, size_of};
use core::ptr::null_mut;
use core::sync::atomic::{AtomicIsize, AtomicPtr, Ordering::*, fence};

#[repr(C)]
pub struct WSDeque {
    size: isize,
    modulo_size: usize,
    top: isize,
    bottom: isize,
    elements: *mut *mut c_void,
}

const _: () = {
    assert!(align_of::<AtomicIsize>() == align_of::<isize>());
    assert!(align_of::<AtomicPtr<c_void>>() == align_of::<*mut c_void>());
};

// Note [Concurrent deque storage]
// -------------------------------
// Layout checks cover the x86-64 C layout and the atomic alignment. The
// deque and its separate slot buffer use the RTS allocator. Concurrent
// operations access indices and slots atomically at their original widths.
// The size, mask and array pointer are
// immutable after publication. Each atomic reference covers one field or slot.
// The caller excludes concurrent operations during collection and destruction.
// The array size is a positive power of two. Live counters are nonnegative
// and do not overflow. One owner may push or pop, and multiple thieves
// may steal.

// User-supplied C compiler flags can enable TSAN without the Hadrian flavour.
// In that case C omits its references. Keep these ELF symbols private even
// if the Rust object is still selected in a shared RTS.
core::arch::global_asm!(
    ".hidden ghc_rust_new_wsdeque",
    ".hidden ghc_rust_free_wsdeque",
    ".hidden ghc_rust_push_wsdeque",
    ".hidden ghc_rust_pop_wsdeque",
    ".hidden ghc_rust_steal_wsdeque_once",
    ".hidden ghc_rust_steal_wsdeque",
);

unsafe extern "C" {
    fn barf(format: *const c_char, ...) -> !;
    fn stgMallocBytes(size: usize, name: *const c_char) -> *mut c_void;
    fn stgFree(pointer: *mut c_void);
}

// The queue has the first power-of-two capacity strictly greater than size.
fn capacity(size: u32) -> usize {
    1usize << (u32::BITS - size.leading_zeros())
}

#[unsafe(no_mangle)]
pub extern "C" fn ghc_rust_new_wsdeque(size: u32) -> *mut WSDeque {
    unsafe {
        if size == 0 {
            barf(c"DeQue,roundUp2: invalid size 0 requested".as_ptr());
        }

        let capacity = capacity(size);
        // Nonzero RTS allocations return aligned storage or terminate.
        let q = stgMallocBytes(size_of::<WSDeque>(), c"newWSDeque".as_ptr()).cast::<WSDeque>();
        let elements = stgMallocBytes(
            capacity * size_of::<*mut c_void>(),
            c"newWSDeque:data space".as_ptr(),
        )
        .cast::<*mut c_void>();

        // Leave the slots uninitialized. Push initializes a slot before
        // publishing it. Initialize the header before taking the atomic view
        // of bottom for the release store.
        q.write(WSDeque {
            size: capacity as isize,
            modulo_size: capacity - 1,
            top: 0,
            bottom: 0,
            elements,
        });
        AtomicIsize::from_ptr(&raw mut (*q).bottom).store(0, Release);
        q
    }
}

/// # Safety
/// The deque must be live and no other operation may access it during or
/// after this call. The caller may free each deque only once.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn ghc_rust_free_wsdeque(q: *mut WSDeque) {
    unsafe {
        stgFree((*q).elements.cast());
        stgFree(q.cast());
    }
}

#[inline(always)]
unsafe fn slot(q: *mut WSDeque, index: usize) -> *mut *mut c_void {
    unsafe { (*q).elements.add(index) }
}

/// # Safety
/// The deque must be live and initialized as described in Note [Concurrent
/// deque storage]. Only the owner may call this function.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn ghc_rust_push_wsdeque(q: *mut WSDeque, elem: *mut c_void) -> bool {
    unsafe {
        let bottom = AtomicIsize::from_ptr(&raw mut (*q).bottom);
        let b = bottom.load(Acquire);
        let t = AtomicIsize::from_ptr(&raw mut (*q).top).load(Acquire);
        if b.wrapping_sub(t) > (*q).size - 1 {
            return false;
        }

        AtomicPtr::from_ptr(slot(q, b as usize & (*q).modulo_size)).store(elem, Relaxed);
        fence(Release);
        bottom.store(b.wrapping_add(1), Relaxed);
        true
    }
}

/// # Safety
/// The deque must be live and initialized as described in Note [Concurrent
/// deque storage]. Only the owner may call this function.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn ghc_rust_pop_wsdeque(q: *mut WSDeque) -> *mut c_void {
    unsafe {
        let bottom = AtomicIsize::from_ptr(&raw mut (*q).bottom);
        let b = bottom.load(Relaxed).wrapping_sub(1);
        bottom.store(b, Relaxed);
        fence(SeqCst);
        let top = AtomicIsize::from_ptr(&raw mut (*q).top);
        let t = top.load(Relaxed);

        let mut result = null_mut();
        if t <= b {
            result = AtomicPtr::from_ptr(slot(q, b as usize & (*q).modulo_size)).load(Relaxed);
            if t < b {
                return result;
            }
            if top
                .compare_exchange(t, t.wrapping_add(1), SeqCst, Relaxed)
                .is_err()
            {
                result = null_mut();
            }
        }
        bottom.store(b.wrapping_add(1), Relaxed);
        result
    }
}

#[inline(always)]
unsafe fn steal_once(q: *mut WSDeque) -> *mut c_void {
    unsafe {
        let top = AtomicIsize::from_ptr(&raw mut (*q).top);
        let t = top.load(Acquire);
        fence(SeqCst);
        let b = AtomicIsize::from_ptr(&raw mut (*q).bottom).load(Acquire);
        if t >= b {
            return null_mut();
        }

        // A live top is nonnegative and size is a power of two.
        let result = AtomicPtr::from_ptr(slot(q, t as usize & (*q).modulo_size)).load(Relaxed);
        if top
            .compare_exchange(t, t.wrapping_add(1), SeqCst, Relaxed)
            .is_err()
        {
            return null_mut();
        }
        result
    }
}

/// # Safety
/// The deque must be live and initialized as described in Note [Concurrent
/// deque storage]. Thieves may call this function concurrently.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn ghc_rust_steal_wsdeque_once(q: *mut WSDeque) -> *mut c_void {
    unsafe { steal_once(q) }
}

/// # Safety
/// The deque must be live and initialized as described in Note [Concurrent
/// deque storage]. Thieves may call this function concurrently.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn ghc_rust_steal_wsdeque(q: *mut WSDeque) -> *mut c_void {
    unsafe {
        loop {
            let result = steal_once(q);
            if !result.is_null() {
                return result;
            }

            // Match looksEmptyWSDeque. Load top before bottom.
            let t = AtomicIsize::from_ptr(&raw mut (*q).top).load(Acquire);
            let b = AtomicIsize::from_ptr(&raw mut (*q).bottom).load(Acquire);
            if b.wrapping_sub(t) <= 0 {
                return null_mut();
            }
        }
    }
}
