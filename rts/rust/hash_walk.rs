use core::ffi::{c_int, c_void};

use super::hash_insert::Table;

pub(super) const SEGMENT_SIZE: usize = 1024;

// The key slot is part of the C visitor API.
#[repr(C)]
pub(super) struct Entry {
    pub(super) key: usize,
    pub(super) value: *const c_void,
    pub(super) next: *mut Entry,
}

/// Visit buckets in descending order and chains from head to tail.
/// Stop when the visitor returns false.
///
/// # Safety
///
/// The table must contain valid segments for its initialized buckets.
/// Their segments and entries must remain allocated during the walk.
/// The caller provides synchronization. A visitor can update a key in place.
unsafe fn walk(table: *mut Table, mut visit: impl FnMut(*mut Entry) -> bool) {
    let directory = unsafe { (&raw const (*table).directory).cast::<*mut *mut Entry>() };
    let buckets = unsafe { (*table).bucket_count as usize };
    for bucket in (0..buckets).rev() {
        let segment = unsafe { directory.add(bucket / SEGMENT_SIZE).read() };
        let mut entry = unsafe { segment.add(bucket % SEGMENT_SIZE).read() };
        while !entry.is_null() {
            if !visit(entry) {
                return;
            }
            entry = unsafe { (&raw const (*entry).next).read() };
        }
    }
}

/// Copy up to capacity keys. A nonpositive capacity permits a null output.
///
/// # Safety
///
/// The table must satisfy the contract of walk. The output must be writable for
/// each copied word and be disjoint from the table.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_hash_keys(
    table: *mut Table,
    output: *mut usize,
    capacity: c_int,
) -> c_int {
    let mut copied = 0;
    if capacity > 0 {
        unsafe {
            walk(table, |entry| {
                output.add(copied as usize).write((*entry).key);
                copied += 1;
                copied < capacity
            });
        }
    }
    copied
}

/// Call the C visitor for each key and value.
///
/// # Safety
///
/// The table must satisfy the contract of walk. The context must be valid for the
/// supplied visitor.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_hash_map(
    table: *mut Table,
    context: *mut c_void,
    visit: Option<unsafe extern "C" fn(*mut c_void, usize, *const c_void)>,
) {
    let Some(visit) = visit else { return };
    unsafe {
        walk(table, |entry| {
            visit(context, (*entry).key, (*entry).value);
            true
        });
    }
}

/// Give the collector the address of each stored key for pointer threading.
///
/// # Safety
///
/// The table must satisfy the contract of walk. The context must be valid for the
/// supplied visitor. The key slots must be writable.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_hash_map_keys(
    table: *mut Table,
    context: *mut c_void,
    visit: Option<unsafe extern "C" fn(*mut c_void, *mut usize, *const c_void)>,
) {
    let Some(visit) = visit else { return };
    unsafe {
        walk(table, |entry| {
            visit(context, &raw mut (*entry).key, (*entry).value);
            true
        });
    }
}

/// Call the C visitor until it returns false or reaches the end.
///
/// # Safety
///
/// The table must satisfy the contract of walk. The context must be valid for the
/// supplied visitor.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_hash_iter(
    table: *mut Table,
    context: *mut c_void,
    visit: Option<unsafe extern "C" fn(*mut c_void, usize, *const c_void) -> bool>,
) {
    let Some(visit) = visit else { return };
    unsafe {
        walk(table, |entry| visit(context, (*entry).key, (*entry).value));
    }
}
