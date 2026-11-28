/*
 * (c)2014 Tweag I/O
 *
 * The Static Pointer Table implementation.
 *
 * https://gitlab.haskell.org/ghc/ghc/wikis/static-pointers
 * https://gitlab.haskell.org/ghc/ghc/wikis/static-pointers/implementation-plan
 *
 */

#include "Rts.h"
#include "StaticPtrTable.h"
#include "RtsUtils.h"
#include "Hash.h"
#include "StablePtr.h"

#if defined(USE_RUST_RTS) && !defined(TSAN_ENABLED)
#define USE_RUST_SPT_ENTRIES 1
GHC_STATIC_ASSERT(sizeof(StgStablePtr) == sizeof(void *) &&
                  _Alignof(StgStablePtr) == _Alignof(void *),
                  "Rust static pointer entry layout");
RTS_PRIVATE StgStablePtr *ghc_rust_spt_new_entry(StgPtr closure);
RTS_PRIVATE void ghc_rust_spt_free_entry(void *entry);
#endif

static HashTable * spt = NULL;

/* Note [Static pointer table lock lifetime]
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Constructors can insert entries before hs_init. Module destructors can
 * remove entries after table teardown. Keep this lock for the process lifetime.
 */
#if defined(THREADED_RTS)
#if defined(HAVE_PTHREAD_H) && !defined(mingw32_HOST_OS)
static Mutex spt_lock = PTHREAD_MUTEX_INITIALIZER;
#elif defined(HAVE_WINDOWS_H)
static Mutex spt_lock = SRWLOCK_INIT;
#endif
#endif

/// Hash function for the SPT.
STATIC_INLINE int hashFingerprint(const HashTable *table, StgWord key) {
  const StgWord64* ptr = (StgWord64*) key;
  // Take half of the key to compute the hash.
  return hashWord(table, *(ptr + 1));
}

/// Comparison function for the SPT.
STATIC_INLINE int compareFingerprint(StgWord a, StgWord b) {
  const StgWord64* ptra = (StgWord64*) a;
  const StgWord64* ptrb = (StgWord64*) b;
  return *ptra == *ptrb && *(ptra + 1) == *(ptrb + 1);
}

void hs_spt_insert_stableptr(StgWord64 key[2], StgStablePtr *entry) {
  // hs_spt_insert is called from constructor functions, so
  // the SPT needs to be initialized here.
  ACQUIRE_LOCK(&spt_lock);
  if (spt == NULL) {
    spt = allocHashTable();
  }
  insertHashTable_(spt, (StgWord)key, entry, hashFingerprint);
  RELEASE_LOCK(&spt_lock);
}

void hs_spt_insert(StgWord64 key[2], void *spe_closure) {
  // Cannot remove this indirection yet because getStablePtr()
  // might return NULL, in which case hs_spt_lookup() returns NULL
  // instead of the actual closure pointer.
#if defined(USE_RUST_SPT_ENTRIES)
  StgStablePtr *entry = ghc_rust_spt_new_entry(spe_closure);
#else
  StgStablePtr * entry = stgMallocBytes( sizeof(StgStablePtr)
                                       , "hs_spt_insert: entry"
                                       );
  *entry = getStablePtr(spe_closure);
#endif
  hs_spt_insert_stableptr(key, entry);
}

static void freeSptEntry(void* entry) {
#if defined(USE_RUST_SPT_ENTRIES)
  ghc_rust_spt_free_entry(entry);
#else
  freeStablePtr(*(StgStablePtr*)entry);
  stgFree(entry);
#endif
}

void hs_spt_remove(StgWord64 key[2]) {
   StgStablePtr* entry = NULL;
   ACQUIRE_LOCK(&spt_lock);
   if (spt != NULL) {
     entry = removeHashTable_(spt, (StgWord)key, NULL,
        hashFingerprint, compareFingerprint);
   }
   RELEASE_LOCK(&spt_lock);

   if (entry)
     freeSptEntry(entry);
}

StgPtr hs_spt_lookup(StgWord64 key[2]) {
  StgPtr ret = NULL;
  ACQUIRE_LOCK(&spt_lock);
  if (spt != NULL) {
    const StgStablePtr * entry = lookupHashTable_(spt, (StgWord)key,
        hashFingerprint, compareFingerprint);
    ret = entry ? deRefStablePtr(*entry) : NULL;
  }
  RELEASE_LOCK(&spt_lock);
  return ret;
}

int hs_spt_keys(StgPtr keys[], int szKeys) {
  int ret = 0;
  ACQUIRE_LOCK(&spt_lock);
  if (spt != NULL) {
    ret = keysHashTable(spt, (StgWord*)keys, szKeys);
  }
  RELEASE_LOCK(&spt_lock);
  return ret;
}

int hs_spt_key_count(void) {
  int ret = 0;
  ACQUIRE_LOCK(&spt_lock);
  if (spt != NULL) {
    ret = keyCountHashTable(spt);
  }
  RELEASE_LOCK(&spt_lock);
  return ret;
}

void exitStaticPtrTable(void) {
  ACQUIRE_LOCK(&spt_lock);
  HashTable *table = spt;
  spt = NULL;
  RELEASE_LOCK(&spt_lock);

  if (table)
    freeHashTable(table, freeSptEntry);
}
