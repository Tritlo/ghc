/* -----------------------------------------------------------------------------
 *
 * (c) The GHC Team, 2007
 *
 * File locking support as required by Haskell
 *
 * ---------------------------------------------------------------------------*/

#include "rts/PosixSource.h"
#include "Rts.h"

#include "FileLock.h"

#if defined(THREADED_RTS)
static Mutex file_lock_mutex;
#endif

#if defined(USE_RUST_RTS)

#include "BeginPrivate.h"

typedef struct RtsRustFileLocks_ RtsRustFileLocks;

RtsRustFileLocks *rts_rust_file_locks_new(void);
void rts_rust_file_locks_free(RtsRustFileLocks *locks);
int rts_rust_file_locks_lock(RtsRustFileLocks *locks,
                            StgWord64 id, StgWord64 dev, StgWord64 ino,
                            int for_writing);
int rts_rust_file_locks_unlock(RtsRustFileLocks *locks, StgWord64 id);

#include "EndPrivate.h"

static RtsRustFileLocks *file_locks;

static void
initRegistry(void)
{
    file_locks = rts_rust_file_locks_new();
}

static void
freeRegistry(void)
{
    rts_rust_file_locks_free(file_locks);
}

static int
lockRegistry(StgWord64 id, StgWord64 dev, StgWord64 ino, int for_writing)
{
    return rts_rust_file_locks_lock(file_locks, id, dev, ino, for_writing);
}

static int
unlockRegistry(StgWord64 id)
{
    return rts_rust_file_locks_unlock(file_locks, id);
}

#else
#include "Hash.h"
#include "RtsUtils.h"

#include <sys/types.h>
#include <unistd.h>
#include <errno.h>

typedef struct {
    StgWord64 device;
    StgWord64 inode;
    int   readers; // >0 : readers,  <0 : writers
} Lock;

// Two hash tables.  The first maps objects (device/inode pairs) to
// Lock objects containing the number of active readers or writers.  The
// second maps file descriptors or file handles to lock objects, so that we can
// unlock by FD or HANDLE without needing to fstat() again.
static HashTable *obj_hash;
static HashTable *key_hash;

STATIC_INLINE int cmpLocks(StgWord w1, StgWord w2)
{
    Lock *l1 = (Lock *)w1;
    Lock *l2 = (Lock *)w2;
    return (l1->device == l2->device && l1->inode == l2->inode);
}

STATIC_INLINE int hashLock(const HashTable *table, StgWord w)
{
    Lock *l = (Lock *)w;
    StgWord key = l->inode ^ (l->inode >> 32) ^ l->device ^ (l->device >> 32);
    // Just xor all 32-bit words of inode and device, hope this is good enough.
    return hashWord(table, key);
}

static void
initRegistry(void)
{
    obj_hash = allocHashTable();
    key_hash  = allocHashTable(); /* ordinary word-based table */
}

static void
freeLock(void *lock)
{
    stgFree(lock);
}

static void
freeRegistry(void)
{
    freeHashTable(obj_hash, freeLock);
    freeHashTable(key_hash,  NULL);
}

static int
lockRegistry(StgWord64 id, StgWord64 dev, StgWord64 ino, int for_writing)
{
    Lock key, *lock;

    key.device = dev;
    key.inode  = ino;

    lock = lookupHashTable_(obj_hash, (StgWord)&key, hashLock, cmpLocks);

    if (lock == NULL)
    {
        lock = stgMallocBytes(sizeof(Lock), "lockFile");
        lock->device = dev;
        lock->inode  = ino;
        lock->readers = for_writing ? -1 : 1;
        insertHashTable_(obj_hash, (StgWord)lock, (void *)lock, hashLock);
        insertHashTable(key_hash, id, lock);
        return 0;
    }
    else
    {
        // single-writer/multi-reader locking:
        if (for_writing || lock->readers < 0) {
            return -1;
        }
        insertHashTable(key_hash, id, lock);
        lock->readers++;
        return 0;
    }
}

static int
unlockRegistry(StgWord64 id)
{
    Lock *lock;

    lock = lookupHashTable(key_hash, id);
    if (lock == NULL) {
        // errorBelch("unlockFile: key %d not found", key);
        // This is normal: we didn't know when calling unlockFile
        // whether this FD referred to a locked file or not.
        return 1;
    }

    if (lock->readers < 0) {
        lock->readers++;
    } else {
        lock->readers--;
    }

    if (lock->readers == 0) {
        removeHashTable_(obj_hash, (StgWord)lock, NULL, hashLock, cmpLocks);
        stgFree(lock);
    }
    removeHashTable(key_hash, id, NULL);
    return 0;
}

#endif /* USE_RUST_RTS */

void
initFileLocking(void)
{
    initRegistry();
#if defined(THREADED_RTS)
    initMutex(&file_lock_mutex);
#endif
}

void
freeFileLocking(void)
{
    freeRegistry();
#if defined(THREADED_RTS)
    closeMutex(&file_lock_mutex);
#endif
}

int
lockFile(StgWord64 id, StgWord64 dev, StgWord64 ino, int for_writing)
{
    ACQUIRE_LOCK(&file_lock_mutex);
    int result = lockRegistry(id, dev, ino, for_writing);
    RELEASE_LOCK(&file_lock_mutex);
    return result;
}

int
unlockFile(StgWord64 id)
{
    ACQUIRE_LOCK(&file_lock_mutex);
    int result = unlockRegistry(id);
    RELEASE_LOCK(&file_lock_mutex);
    return result;
}
