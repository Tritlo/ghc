use core::ffi::{c_char, c_int, c_void};
use core::mem::size_of;
use core::ptr::{null, with_exposed_provenance};

use super::hash_api::{
    HashTable, allocHashTable, freeHashTable, hashWord, insertHashTable, insertHashTable_,
    lookupHashTable_, removeHashTable, removeHashTable_,
};

unsafe extern "C" {
    fn stgMallocBytes(size: usize, msg: *const c_char) -> *mut c_void;
    fn stgFree(ptr: *mut c_void);
}

#[derive(PartialEq, Eq)]
struct FileIdentity {
    device: u64,
    inode: u64,
}

enum Holders {
    Readers(u32),
    Writer,
}

struct Lock {
    file: FileIdentity,
    holders: Holders,
}

// The RTS startup and shutdown hooks own the registry lifetime. The caller
// holds the file-lock mutex for each operation in the threaded RTS.
pub(super) struct Registry {
    files: *mut HashTable,
    handles: *mut HashTable,
}

// The C table stores a pointer to a FileIdentity as a StgWord. A lookup
// uses a stack key during the call. A stored key remains valid until removal.
unsafe extern "C" fn compare_files(a: usize, b: usize) -> c_int {
    unsafe {
        (*with_exposed_provenance::<FileIdentity>(a) == *with_exposed_provenance::<FileIdentity>(b))
            .into()
    }
}

unsafe extern "C" fn hash_file(table: *const HashTable, key: usize) -> c_int {
    unsafe {
        let file = &*with_exposed_provenance::<FileIdentity>(key);
        let folded = file.inode ^ (file.inode >> 32) ^ file.device ^ (file.device >> 32);
        hashWord(table, folded as usize)
    }
}

#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn rts_rust_file_locks_new() -> *mut Registry {
    unsafe {
        let registry =
            stgMallocBytes(size_of::<Registry>(), c"initFileLocking".as_ptr()).cast::<Registry>();
        registry.write(Registry {
            files: allocHashTable(),
            handles: allocHashTable(),
        });
        registry
    }
}

#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn rts_rust_file_locks_free(registry: *mut Registry) {
    unsafe {
        freeHashTable((*registry).files, Some(stgFree));
        freeHashTable((*registry).handles, None);
        stgFree(registry.cast());
    }
}

#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn rts_rust_file_locks_lock(
    registry: *mut Registry,
    id: u64,
    device: u64,
    inode: u64,
    for_writing: c_int,
) -> c_int {
    unsafe {
        let registry = &*registry;
        let file = FileIdentity { device, inode };
        let mut lock = lookupHashTable_(
            registry.files,
            (&raw const file).expose_provenance(),
            hash_file,
            compare_files,
        )
        .cast::<Lock>();

        if lock.is_null() {
            lock = stgMallocBytes(size_of::<Lock>(), c"lockFile".as_ptr()).cast::<Lock>();
            lock.write(Lock {
                file,
                holders: if for_writing != 0 {
                    Holders::Writer
                } else {
                    Holders::Readers(1)
                },
            });
            insertHashTable_(
                registry.files,
                (&raw const (*lock).file).expose_provenance(),
                lock.cast(),
                hash_file,
            );
        } else {
            match &mut (*lock).holders {
                Holders::Readers(count) if for_writing == 0 => *count += 1,
                _ => return -1,
            }
        }

        // A repeated ID adds a binding. The RTS table selects which binding
        // to remove, including when a bucket split changes their order.
        insertHashTable(registry.handles, id as usize, lock.cast());
        0
    }
}

#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn rts_rust_file_locks_unlock(
    registry: *mut Registry,
    id: u64,
) -> c_int {
    unsafe {
        let registry = &*registry;
        let lock = removeHashTable(registry.handles, id as usize, null()).cast::<Lock>();
        if lock.is_null() {
            return 1;
        }

        match &mut (*lock).holders {
            Holders::Readers(count) if *count > 1 => *count -= 1,
            _ => {
                removeHashTable_(
                    registry.files,
                    (&raw const (*lock).file).expose_provenance(),
                    null(),
                    hash_file,
                    compare_files,
                );
                stgFree(lock.cast());
            }
        }
        0
    }
}
