use core::ffi::{c_char, c_void};
use core::mem::{align_of, size_of};
use core::ptr::{copy_nonoverlapping, null_mut};
use core::sync::atomic::{
    AtomicPtr,
    Ordering::{Relaxed, Release},
};

type Entry = *mut c_void;

const _: () = {
    assert!(size_of::<AtomicPtr<c_void>>() == size_of::<Entry>());
    assert!(align_of::<AtomicPtr<c_void>>() == align_of::<Entry>());
};

// The common object is also linked when C retains its TSAN-instrumented path.
core::arch::global_asm!(
    ".hidden ghc_rust_init_stable_ptr_table",
    ".hidden ghc_rust_exit_stable_ptr_table",
    ".hidden ghc_rust_take_stable_ptr",
    ".hidden ghc_rust_release_stable_ptr",
    ".hidden ghc_rust_grow_stable_ptr_table",
    ".hidden ghc_rust_free_old_stable_ptr_tables",
);

unsafe extern "C" {
    fn stgMallocBytes(size: usize, label: *const c_char) -> *mut c_void;
    fn stgFree(allocation: *mut c_void);
}

// See Note [Enlarging the stable pointer table] in StablePtr.c.
static mut RETIRED: [*mut Entry; usize::BITS as usize] = [null_mut(); usize::BITS as usize];
static mut RETIRED_COUNT: usize = 0;

/// Allocate the first table before the RTS publishes any handles.
/// C serializes initialization and passes a nonzero initialized capacity.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_init_stable_ptr_table(
    table: *mut *mut Entry,
    head: *mut *mut Entry,
    count: usize,
) {
    unsafe {
        let first = stgMallocBytes(count * size_of::<Entry>(), c"initStablePtrTable".as_ptr())
            .cast::<Entry>();
        link_free_entries(first, count);
        head.write(first);
        AtomicPtr::from_ptr(table).store(first, Release);
    }
}

/// Release all table versions after shutdown stops table users.
/// The current table may be null.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_exit_stable_ptr_table(
    table: *mut *mut Entry,
    head: *mut *mut Entry,
) {
    unsafe {
        let active = AtomicPtr::from_ptr(table);
        let current = active.load(Relaxed);
        if !current.is_null() {
            stgFree(current.cast());
        }
        active.store(null_mut(), Relaxed);
        head.write(null_mut());
        ghc_rust_free_old_stable_ptr_tables();
    }
}

/// Double the full table and retain its previous storage until collection.
/// C holds the table mutex. It checks capacity overflow before this call.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_grow_stable_ptr_table(
    table: *mut *mut Entry,
    head: *mut *mut Entry,
    old_count: usize,
) {
    unsafe {
        let active = AtomicPtr::from_ptr(table);
        let old = active.load(Relaxed);
        let new = stgMallocBytes(
            2 * old_count * size_of::<Entry>(),
            c"enlargeStablePtrTable".as_ptr(),
        )
        .cast::<Entry>();
        copy_nonoverlapping(old, new, old_count);
        let tail = new.add(old_count);
        link_free_entries(tail, old_count);
        head.write(tail);

        // Each outstanding retirement corresponds to a doubling. The checked
        // capacity therefore bounds the index by the number of word bits.
        (&raw mut RETIRED)
            .cast::<*mut Entry>()
            .add(RETIRED_COUNT)
            .write(old);
        RETIRED_COUNT += 1;

        // Keep the previous storage valid for readers that loaded its base.
        active.store(new, Release);
    }
}

/// Reclaim retired storage after C stops readers, during mark or shutdown.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_free_old_stable_ptr_tables() {
    unsafe {
        let tables = (&raw const RETIRED).cast::<*mut Entry>();
        for index in 0..RETIRED_COUNT {
            stgFree(tables.add(index).read().cast());
        }
        RETIRED_COUNT = 0;
    }
}

/// Link a new range of table entries in index order. None has a live handle.
unsafe fn link_free_entries(table: *mut Entry, count: usize) {
    let mut next = null_mut();
    for index in (0..count).rev() {
        let slot = unsafe { table.add(index) };
        unsafe { slot.write(next) };
        next = slot.cast();
    }
}

/// Take the head slot and publish its value for acquire loads in deRefStablePtr.
/// C holds the table mutex and supplies a nonempty free list in this table.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_take_stable_ptr(
    table: *mut Entry,
    head: *mut *mut Entry,
    value: Entry,
) -> usize {
    unsafe {
        let slot = head.read();
        head.write(slot.read().cast());
        AtomicPtr::from_ptr(slot).store(value, Release);
        slot.offset_from_unsigned(table)
    }
}

/// Return a live slot to the free list. C holds the table mutex.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_release_stable_ptr(
    head: *mut *mut Entry,
    slot: *mut Entry,
) {
    unsafe {
        AtomicPtr::from_ptr(slot).store(head.read().cast(), Relaxed);
        head.write(slot);
    }
}

/// Visit live entries in table order. See Note [Stable pointer root slots] in StablePtr.c.
///
/// # Safety
///
/// The caller keeps the table stable during the scan. For a nonzero count,
/// the table contains that many initialized, pointer-sized entries. The
/// caller supplies a valid callback if the table contains live entries.
/// The collector may update the pointer in each slot passed to its callback.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_visit_stable_ptrs(
    table: *mut *mut c_void,
    count: usize,
    visit: Option<unsafe extern "C" fn(*mut c_void, *mut *mut c_void)>,
    user: *mut c_void,
) {
    let bytes = count * size_of::<*mut c_void>();
    for index in 0..count {
        let slot = unsafe { table.add(index) };
        let root = unsafe { slot.read() };
        if !root.is_null() && root.addr().wrapping_sub(table.addr()) >= bytes {
            unsafe { visit.unwrap_unchecked()(user, slot) };
        }
    }
}
