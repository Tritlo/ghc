use core::{
    ffi::{c_char, c_void},
    mem::size_of,
    ptr,
    sync::atomic::{AtomicPtr, Ordering},
};

use super::hash_api::{
    HashTable, allocHashTable, freeHashTable, insertHashTable, keyCountHashTable, removeHashTable,
};

core::arch::global_asm!(
    ".hidden ghc_rust_init_stable_name_table",
    ".hidden ghc_rust_grow_stable_name_table",
    ".hidden ghc_rust_exit_stable_name_table",
    ".hidden ghc_rust_reserve_stable_name",
    ".hidden ghc_rust_gc_stable_name_table",
    ".hidden ghc_rust_sweep_stable_names",
    ".hidden ghc_rust_stable_name_key",
);

unsafe extern "C" {
    fn stgMallocBytes(size: usize, label: *const c_char) -> *mut c_void;
    fn stgReallocBytes(allocation: *mut c_void, size: usize, label: *const c_char) -> *mut c_void;
    fn stgFree(allocation: *mut c_void);
}

#[repr(C)]
pub(super) struct Entry {
    addr: *mut c_void,
    old: *mut c_void,
    sn_obj: *mut c_void,
}

// StableName.c checks these against the native closure layout.
const TAG_MASK: usize = 7;
const IND: u32 = 27;
const IND_STATIC: u32 = 28;
const BLACKHOLE: u32 = 38;

// See Note [Stable name key] in StableName.c.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_stable_name_key(
    mut current: *mut c_void,
    info_type_offset: isize,
    indirectee_offset: usize,
) -> *mut c_void {
    unsafe {
        loop {
            let untagged = current.map_addr(|addr| addr & !TAG_MASK);
            let info = AtomicPtr::<u8>::from_ptr(untagged.cast()).load(Ordering::Relaxed);
            let closure_kind = info.wrapping_offset(info_type_offset).cast::<u32>().read();
            if closure_kind == IND || closure_kind == IND_STATIC || closure_kind == BLACKHOLE {
                let indirectee = AtomicPtr::from_ptr(
                    untagged.cast::<u8>().add(indirectee_offset).cast::<*mut c_void>(),
                )
                .load(Ordering::Acquire);
                if closure_kind != BLACKHOLE || indirectee.addr() & TAG_MASK != 0 {
                    current = indirectee;
                    continue;
                }
                return indirectee;
            }
            return untagged;
        }
    }
}

/// Allocate the first table. Slot zero stays unused.
/// C initializes the hash table and mutex after this call.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_init_stable_name_table(
    table: *mut *mut Entry,
    head: *mut *mut Entry,
    count: usize,
) {
    unsafe {
        let first = stgMallocBytes(count * size_of::<Entry>(), c"initStableNameTable".as_ptr())
            .cast::<Entry>();
        table.write(first);
        let free = first.add(1);
        link_free_entries(free, count - 1);
        head.write(free);
    }
}

/// Grow an exhausted table. C holds the table mutex and checks size overflow.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_grow_stable_name_table(
    table: *mut *mut Entry,
    head: *mut *mut Entry,
    old_count: usize,
) {
    unsafe {
        let grown = stgReallocBytes(
            table.read().cast(),
            2 * old_count * size_of::<Entry>(),
            c"enlargeStableNameTable".as_ptr(),
        )
        .cast::<Entry>();
        table.write(grown);
        let free = grown.add(old_count);
        link_free_entries(free, old_count);
        head.write(free);
    }
}

/// Free the table at shutdown. C frees the hash table first.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_exit_stable_name_table(table: *mut *mut Entry) {
    unsafe {
        let current = table.read();
        if !current.is_null() {
            stgFree(current.cast());
        }
        table.write(ptr::null_mut());
    }
}

/// Link a new range in ascending slot order.
unsafe fn link_free_entries(first: *mut Entry, count: usize) {
    let mut next = ptr::null_mut();
    for index in (0..count).rev() {
        let slot = unsafe { first.add(index) };
        unsafe {
            (*slot).addr = next;
            (*slot).old = ptr::null_mut();
            (*slot).sn_obj = ptr::null_mut();
        }
        next = slot.cast();
    }
}

/// Take one free slot and add its address to the index.
/// C holds the table lock and publishes the name object after this call.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_reserve_stable_name(
    table: *mut Entry,
    head: *mut *mut Entry,
    hash: *mut HashTable,
    addr: *mut c_void,
) -> usize {
    unsafe {
        let slot = head.read();
        head.write((*slot).addr.cast());
        (*slot).addr = addr;
        (*slot).sn_obj = ptr::null_mut();
        let index = slot.offset_from_unsigned(table);
        insertHashTable(hash, addr.addr(), ptr::with_exposed_provenance(index));
        index
    }
}

// See Note [Stable name table visits] in StableName.h. Callers serialize
// changes to the table and allow the collector to rewrite individual slots.
unsafe fn visit_entries(table: *mut Entry, count: usize, mut visit: impl FnMut(usize, *mut Entry)) {
    let bytes = count * size_of::<Entry>();
    for index in 1..count {
        let entry = unsafe { table.add(index) };
        let addr = unsafe { (*entry).addr };
        if addr.addr().wrapping_sub(table.addr()) >= bytes {
            visit(index, entry);
        }
    }
}

/// Save each visited address before the collector moves the pointee.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_remember_stable_names(table: *mut Entry, count: usize) {
    unsafe { visit_entries(table, count, |_, entry| (*entry).old = (*entry).addr) };
}

/// Give the collector each non-null name slot, then its non-null pointee slot.
/// The collector can update the slots in place.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_thread_stable_names(
    table: *mut Entry,
    count: usize,
    evac: Option<unsafe extern "C" fn(*mut c_void, *mut *mut c_void)>,
    user: *mut c_void,
) {
    unsafe {
        visit_entries(table, count, |_, entry| {
            if !(*entry).sn_obj.is_null() {
                evac.unwrap_unchecked()(user, &raw mut (*entry).sn_obj);
            }
            if !(*entry).addr.is_null() {
                evac.unwrap_unchecked()(user, &raw mut (*entry).addr);
            }
        });
    }
}

/// Update the address index after the collector visits stable names.
/// C serializes access to the entries and the hash table.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_update_stable_names(
    table: *mut Entry,
    count: usize,
    hash: *mut *mut HashTable,
    full: bool,
) {
    unsafe {
        let mut index_by_addr = hash.read();
        if full && !index_by_addr.is_null() && keyCountHashTable(index_by_addr) != 0 {
            freeHashTable(index_by_addr, None);
            index_by_addr = allocHashTable();
            hash.write(index_by_addr);
        }

        visit_entries(table, count, |index, entry| {
            let addr = (*entry).addr;
            if !full {
                let old = (*entry).old;
                if addr == old {
                    return;
                }
                removeHashTable(index_by_addr, old.addr(), ptr::null());
            }
            if !addr.is_null() {
                insertHashTable(
                    index_by_addr,
                    addr.addr(),
                    ptr::with_exposed_provenance(index),
                );
            }
        });
    }
}

// See Note [Stable name liveness pass] in StableName.c.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_gc_stable_name_table(
    table: *mut Entry,
    count: usize,
    free: *mut *mut Entry,
    hash: *mut HashTable,
    is_alive: unsafe extern "C" fn(*mut c_void) -> *mut c_void,
    trace_dead_name: Option<unsafe extern "C" fn(usize, *mut c_void)>,
    trace_dead_pointee: Option<unsafe extern "C" fn(usize)>,
) {
    unsafe {
        visit_entries(table, count, |index, entry| {
            let name = (*entry).sn_obj;
            if name.is_null() {
                return;
            }
            let live_name = is_alive(name);
            (*entry).sn_obj = live_name;
            if live_name.is_null() {
                if let Some(trace) = trace_dead_name {
                    trace(index, (*entry).addr);
                }
                free_stable_name(entry, free, hash);
            } else {
                let addr = (*entry).addr;
                if !addr.is_null() {
                    let live_addr = is_alive(addr);
                    (*entry).addr = live_addr;
                    if live_addr.is_null() {
                        if let Some(trace) = trace_dead_pointee {
                            trace(index);
                        }
                    }
                }
            }
        });
    }
}

/// Sweep names from the nonmoving snapshot without rewriting live slots.
/// C holds the table lock and supplies the snapshot liveness predicate.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_sweep_stable_names(
    table: *mut Entry,
    count: usize,
    free: *mut *mut Entry,
    hash: *mut HashTable,
    is_alive: unsafe extern "C" fn(*mut c_void) -> bool,
) {
    unsafe {
        visit_entries(table, count, |_, entry| {
            let name = (*entry).sn_obj;
            if name.is_null() {
                return;
            }
            if !is_alive(name) {
                (*entry).sn_obj = ptr::null_mut();
                free_stable_name(entry, free, hash);
            } else {
                let addr = (*entry).addr;
                if !addr.is_null() && !is_alive(addr) {
                    (*entry).addr = ptr::null_mut();
                }
            }
        });
    }
}

/// Return a dead name entry to the free list. The caller holds the table lock.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_free_stable_name(
    entry: *mut Entry,
    head: *mut *mut Entry,
    hash: *mut HashTable,
) {
    unsafe { free_stable_name(entry, head, hash) }
}

unsafe fn free_stable_name(entry: *mut Entry, head: *mut *mut Entry, hash: *mut HashTable) {
    unsafe {
        removeHashTable(hash, (*entry).old.addr(), ptr::null());
        (*entry).addr = head.read().cast();
        head.write(entry);
    }
}
