use core::{
    ffi::{c_char, c_int, c_void},
    mem::size_of,
    ptr,
};

use super::hash_walk::{Entry, SEGMENT_SIZE};

const CHUNK_ENTRIES: usize = 1024 * size_of::<usize>() / size_of::<Entry>();

const DIRECTORY_SIZE: usize = 1024;
const LOAD: c_int = 5;

// The C API uses only opaque pointers to this table.
#[repr(C)]
pub(super) struct Table {
    split: c_int,
    max: c_int,
    mask1: c_int,
    mask2: c_int,
    key_count: c_int,
    pub(super) bucket_count: c_int,
    pub(super) directory: [*mut *mut Entry; DIRECTORY_SIZE],
    free_list: *mut Entry,
    chunks: *mut Chunk,
}

#[repr(C)]
struct Chunk {
    next: *mut Chunk,
    entries: [Entry; CHUNK_ENTRIES],
}

pub(super) type Hash = unsafe extern "C" fn(*const Table, usize) -> c_int;

unsafe extern "C" {
    fn barf(format: *const c_char, ...) -> !;
    fn stgMallocBytes(size: usize, label: *const c_char) -> *mut c_void;
    fn stgFree(ptr: *mut c_void);
    fn strlen(value: *const c_char) -> usize;
    fn ghc_c_hash_buffer(buf: *const c_void, len: usize) -> usize;
}

unsafe fn segment_slot(table: *mut Table, segment: usize) -> *mut *mut *mut Entry {
    let directory = unsafe { (&raw mut (*table).directory).cast::<*mut *mut Entry>() };
    unsafe { directory.add(segment) }
}

unsafe fn alloc_segment(table: *mut Table, segment: usize) -> *mut *mut Entry {
    unsafe {
        let buckets = stgMallocBytes(
            SEGMENT_SIZE * size_of::<*mut Entry>(),
            c"allocSegment".as_ptr(),
        )
        .cast();
        segment_slot(table, segment).write(buckets);
        buckets
    }
}

unsafe fn alloc_entry(table: *mut Table) -> *mut Entry {
    unsafe {
        let entry = (*table).free_list;
        if !entry.is_null() {
            (*table).free_list = (*entry).next;
            return entry;
        }

        let chunk = stgMallocBytes(size_of::<Chunk>(), c"allocHashList".as_ptr()).cast::<Chunk>();
        (*chunk).next = (*table).chunks;
        (*table).chunks = chunk;
        let entries = (&raw mut (*chunk).entries).cast::<Entry>();
        // Return the first entry and link the rest in address order.
        (*table).free_list = entries.add(1);
        for index in 1..CHUNK_ENTRIES - 1 {
            (*entries.add(index)).next = entries.add(index + 1);
        }
        (*entries.add(CHUNK_ENTRIES - 1)).next = ptr::null_mut();
        entries
    }
}

/// Return a detached entry to its table and return its value.
/// The caller must own the table exclusively. A non-null entry must come from it.
pub(super) unsafe fn recycle_entry(table: *mut Table, entry: *mut Entry) -> *const c_void {
    if entry.is_null() {
        return ptr::null();
    }
    unsafe {
        (*entry).next = (*table).free_list;
        (*table).free_list = entry;
        (*table).key_count -= 1;
        (*entry).value
    }
}

/// Allocate an empty table and its initial segment.
#[unsafe(no_mangle)]
pub(super) extern "C" fn ghc_rust_hash_alloc() -> *mut Table {
    unsafe {
        let table = stgMallocBytes(size_of::<Table>(), c"allocHashTable".as_ptr()).cast::<Table>();
        let buckets = alloc_segment(table, 0);
        for index in 0..SEGMENT_SIZE {
            buckets.add(index).write(ptr::null_mut());
        }
        (*table).split = 0;
        (*table).max = SEGMENT_SIZE as c_int;
        (*table).mask1 = SEGMENT_SIZE as c_int - 1;
        (*table).mask2 = 2 * SEGMENT_SIZE as c_int - 1;
        (*table).key_count = 0;
        (*table).bucket_count = SEGMENT_SIZE as c_int;
        (*table).free_list = ptr::null_mut();
        (*table).chunks = ptr::null_mut();
        table
    }
}

/// Release all table storage and optionally visit each live value.
/// The caller must own the table exclusively. The callback may free its value
/// but must not mutate or free the table.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_hash_free(
    table: *mut Table,
    free_value: Option<unsafe extern "C" fn(*mut c_void)>,
) {
    unsafe {
        let buckets = (*table).bucket_count as usize;
        for segment in (0..buckets.div_ceil(SEGMENT_SIZE)).rev() {
            let slots = segment_slot(table, segment).read();
            if let Some(free_value) = free_value {
                let count = (buckets - segment * SEGMENT_SIZE).min(SEGMENT_SIZE);
                for index in (0..count).rev() {
                    let mut entry = slots.add(index).read();
                    while !entry.is_null() {
                        let next = (*entry).next;
                        free_value((*entry).value.cast_mut());
                        entry = next;
                    }
                }
            }
            stgFree(slots.cast());
        }
        let mut chunk = (*table).chunks;
        while !chunk.is_null() {
            let next = (*chunk).next;
            stgFree(chunk.cast());
            chunk = next;
        }
        stgFree(table.cast());
    }
}

// Select the bucket in the larger table only if the smaller bucket has split.
unsafe fn select_bucket(table: *const Table, hash: usize) -> c_int {
    unsafe {
        let bucket = (hash & (*table).mask1 as usize) as c_int;
        if bucket < (*table).split {
            (hash & (*table).mask2 as usize) as c_int
        } else {
            bucket
        }
    }
}

/// The table must be initialized and stable during bucket selection.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_hash_word(table: *const Table, key: usize) -> c_int {
    unsafe { select_bucket(table, key / size_of::<usize>()) }
}

/// The table must be stable and the buffer must contain len accessible bytes.
/// The native primitive accepts a null buffer when len is zero.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_hash_buffer(
    table: *const Table,
    buf: *const c_void,
    len: usize,
) -> c_int {
    unsafe { select_bucket(table, ghc_c_hash_buffer(buf, len)) }
}

/// The table must be stable and the key must point to a C string.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_hash_str(table: *const Table, key: usize) -> c_int {
    let string = key as *const c_char;
    unsafe { ghc_rust_hash_buffer(table, string.cast(), strlen(string)) }
}

/// The table must be initialized and readable.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_hash_count(table: *const Table) -> c_int {
    unsafe { (*table).key_count }
}

pub(super) unsafe fn bucket_slot(table: *mut Table, index: usize) -> *mut *mut Entry {
    unsafe {
        segment_slot(table, index / SEGMENT_SIZE)
            .read()
            .add(index % SEGMENT_SIZE)
    }
}

unsafe fn expand(table: *mut Table, hash: impl Fn(*const Table, usize) -> c_int) {
    unsafe {
        let old_bucket = (*table).split as usize;
        let new_bucket = old_bucket + (*table).max as usize;
        if new_bucket == DIRECTORY_SIZE * SEGMENT_SIZE {
            return;
        }

        if new_bucket.is_multiple_of(SEGMENT_SIZE) {
            alloc_segment(table, new_bucket / SEGMENT_SIZE);
        }
        let old_slot = bucket_slot(table, old_bucket);
        let new_slot = bucket_slot(table, new_bucket);

        // Publish the initialized bucket and new limits before hashing any
        // entry. A custom hash function can inspect the table during the split.
        new_slot.write(ptr::null_mut());
        (*table).split += 1;
        if (*table).split == (*table).max {
            (*table).split = 0;
            (*table).max *= 2;
            (*table).mask1 = (*table).mask2;
            (*table).mask2 = ((*table).mask2 << 1) | 1;
        }
        (*table).bucket_count += 1;

        // Visit the old chain in order. Prepend to each output chain, as in C.
        // Save the next pointer before the callback and publish both heads
        // only after the walk.
        let mut old_head = ptr::null_mut();
        let mut new_head = ptr::null_mut();
        let mut entry = old_slot.read();
        while !entry.is_null() {
            let next = (*entry).next;
            if hash(table, (*entry).key) as usize == new_bucket {
                (*entry).next = new_head;
                new_head = entry;
            } else {
                (*entry).next = old_head;
                old_head = entry;
            }
            entry = next;
        }
        old_slot.write(old_head);
        new_slot.write(new_head);
    }
}

unsafe fn insert(
    table: *mut Table,
    key: usize,
    value: *const c_void,
    hash: impl Fn(*const Table, usize) -> c_int + Copy,
) {
    unsafe {
        if (*table).key_count == c_int::MAX {
            barf(c"insertHashTable: too many entries".as_ptr());
        }
        (*table).key_count += 1;
        if (*table).key_count >= LOAD * (*table).bucket_count {
            expand(table, hash);
        }
        let slot = bucket_slot(table, hash(table, key) as usize);

        let entry = alloc_entry(table);
        entry.write(Entry {
            key,
            value,
            next: slot.read(),
        });
        slot.write(entry);
    }
}

/// Insert a word key, splitting a bucket when the load reaches the limit.
///
/// # Safety
/// The table must be initialized and the caller must exclude concurrent or
/// reentrant mutation.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_hash_insert_word(
    table: *mut Table,
    key: usize,
    value: *const c_void,
) {
    unsafe {
        insert(table, key, value, |table, key| {
            ghc_rust_hash_word(table, key)
        })
    }
}

/// Insert a C string key. All affected keys must be valid C strings.
/// The caller must exclude concurrent and reentrant mutation.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_hash_insert_str(
    table: *mut Table,
    key: usize,
    value: *const c_void,
) {
    unsafe {
        insert(table, key, value, |table, key| {
            ghc_rust_hash_str(table, key)
        })
    }
}

/// Insert a key using a C hash function.
///
/// # Safety
/// The table must be initialized. The caller must exclude concurrent and
/// reentrant mutation. The callback must accept all keys in the affected
/// bucket and return an initialized bucket index. It may inspect the table.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_hash_insert_custom(
    table: *mut Table,
    key: usize,
    value: *const c_void,
    hash: Hash,
) {
    unsafe { insert(table, key, value, |table, key| hash(table, key)) }
}
