/*-----------------------------------------------------------------------------
 *
 * (c) The AQUA Project, Glasgow University, 1995-1998
 * (c) The GHC Team, 1999
 *
 * Dynamically expanding linear hash tables, as described in
 * Per-\AAke Larson, ``Dynamic Hash Tables,'' CACM 31(4), April 1988,
 * pp. 446 -- 457.
 * -------------------------------------------------------------------------- */

#include "rts/PosixSource.h"
#include "Rts.h"

#include "Hash.h"
#include "RtsUtils.h"

#define XXH_INLINE_ALL

#include "xxhash.h"

#include <limits.h>
#include <string.h>

#if !defined(USE_RUST_RTS)
#define HSEGSIZE    1024    /* Size of a single hash table segment */
                            /* Also the minimum size of a hash table */
#define HDIRSIZE    1024    /* Size of the segment directory */
                            /* Maximum hash table size is HSEGSIZE * HDIRSIZE */
#define HLOAD       5       /* Maximum average load of a single hash bucket */

#define HCHUNK      (1024 * sizeof(W_) / sizeof(HashList))
                            /* Number of HashList cells to allocate in one go */


/* Linked list of (key, data) pairs for separate chaining */
typedef struct hashlist {
    StgWord key;
    const void *data;
    struct hashlist *next;  /* Next cell in bucket chain (same hash value) */
} HashList;

typedef struct chunklist {
  struct chunklist *next;
} HashListChunk;

struct hashtable {
    int split;              /* Next bucket to split when expanding */
    int max;                /* Max bucket of smaller table */
    int mask1;              /* Mask for doing the mod of h_1 (smaller table) */
    int mask2;              /* Mask for doing the mod of h_2 (larger table) */
    int kcount;             /* Number of keys */
    int bcount;             /* Number of buckets */
    HashList **dir[HDIRSIZE];   /* Directory of segments */
    HashList *freeList;         /* free list of HashLists */
    HashListChunk *chunks;      /* list of HashListChunks so we can later free them */
};

#else
RTS_PRIVATE void ghc_rust_hash_insert_word(HashTable *table, StgWord key, const void *data);
RTS_PRIVATE void ghc_rust_hash_insert_str(HashTable *table, StgWord key, const void *data);
RTS_PRIVATE void ghc_rust_hash_insert_custom(HashTable *table, StgWord key, const void *data,
                                              HashFunction hash);
RTS_PRIVATE HashTable *ghc_rust_hash_alloc(void);
RTS_PRIVATE void ghc_rust_hash_free(HashTable *table, void (*freeDataFun)(void *));
RTS_PRIVATE int ghc_rust_hash_word(const HashTable *table, StgWord key);
RTS_PRIVATE int ghc_rust_hash_buffer(const HashTable *table, const void *buf, size_t len);
RTS_PRIVATE int ghc_rust_hash_str(const HashTable *table, StgWord key);
RTS_PRIVATE int ghc_rust_hash_count(const HashTable *table);
RTS_PRIVATE StgWord ghc_c_hash_buffer(const void *buf, size_t len);

RTS_PRIVATE int ghc_rust_hash_keys(HashTable *table, StgWord *keys, int capacity);
RTS_PRIVATE void ghc_rust_hash_map(HashTable *table, void *data, MapHashFn fn);
RTS_PRIVATE void ghc_rust_hash_map_keys(HashTable *table, void *data, MapHashFnKeys fn);
RTS_PRIVATE void ghc_rust_hash_iter(HashTable *table, void *data, IterHashFn fn);

RTS_PRIVATE const void *ghc_rust_hash_lookup_word(const HashTable *table, StgWord key);
RTS_PRIVATE const void *ghc_rust_hash_lookup_str(const HashTable *table, StgWord key);
RTS_PRIVATE const void *ghc_rust_hash_lookup_custom(const HashTable *table, StgWord key,
                                                   HashFunction hash, CompareFunction cmp);
RTS_PRIVATE const void *ghc_rust_hash_remove_word(HashTable *table, StgWord key, const void *data);
RTS_PRIVATE const void *ghc_rust_hash_remove_str(HashTable *table, StgWord key, const void *data);
RTS_PRIVATE const void *ghc_rust_hash_remove_custom(HashTable *table, StgWord key, const void *data,
                                                    HashFunction hash, CompareFunction cmp);
#endif

/* Use the same bundled xxHash primitive in both implementations. */
STATIC_INLINE StgWord hashBytes(const void *buf, size_t len)
{
#if WORD_SIZE_IN_BITS == 64
    return XXH3_64bits_withSeed(buf, len, 1048583);
#else
    return XXH32(buf, len, 1048583);
#endif
}

#if defined(USE_RUST_RTS)
StgWord ghc_c_hash_buffer(const void *buf, size_t len)
{
    return hashBytes(buf, len);
}
#else
/* Create an identical structure, but is distinct on a type level,
 * for string hash table. Since it's a direct embedding of
 * a hashtable and not a reference, there shouldn't be
 * any overhead post-compilation.  */
struct strhashtable { struct hashtable table; };
#endif

/* -----------------------------------------------------------------------------
 * Hash first using the smaller table.  If the bucket is less than the
 * next bucket to be split, re-hash using the larger table.
 * -------------------------------------------------------------------------- */
int
hashWord(const HashTable *table, StgWord key)
{
#if defined(USE_RUST_RTS)
    return ghc_rust_hash_word(table, key);
#else
    int bucket;

    /* Strip the boring zero bits */
    key /= sizeof(StgWord);

    /* Mod the size of the hash table (a power of 2) */
    bucket = key & table->mask1;

    if (bucket < table->split) {
        /* Mod the size of the expanded hash table (also a power of 2) */
        bucket = key & table->mask2;
    }
    return bucket;
#endif
}

int
hashBuffer(const HashTable *table, const void *buf, size_t len)
{
#if defined(USE_RUST_RTS)
    return ghc_rust_hash_buffer(table, buf, len);
#else
    StgWord h = hashBytes(buf, len);

    /* Mod the size of the hash table (a power of 2) */
    int bucket = h & table->mask1;

    if (bucket < table->split) {
        /* Mod the size of the expanded hash table (also a power of 2) */
        bucket = h & table->mask2;
    }

    return bucket;
#endif
}

int
hashStr(const HashTable *table, StgWord w)
{
#if defined(USE_RUST_RTS)
    return ghc_rust_hash_str(table, w);
#else
    const char *key = (char*) w;
    return hashBuffer(table, key, strlen(key));
#endif
}

#if !defined(USE_RUST_RTS)
STATIC_INLINE int
compareWord(StgWord key1, StgWord key2)
{
    return (key1 == key2);
}

STATIC_INLINE int
compareStr(StgWord key1, StgWord key2)
{
    return (strcmp((char *)key1, (char *)key2) == 0);
}


/* -----------------------------------------------------------------------------
 * Allocate a new segment of the dynamically growing hash table.
 * -------------------------------------------------------------------------- */

STATIC_INLINE void
allocSegment(HashTable *table, int segment)
{
    table->dir[segment] = stgMallocBytes(HSEGSIZE * sizeof(HashList *),
                                         "allocSegment");
}


/* -----------------------------------------------------------------------------
 * Expand the larger hash table by one bucket, and split one bucket
 * from the smaller table into two parts.  Only the bucket referenced
 * by @table->split@ is affected by the expansion.
 * -------------------------------------------------------------------------- */

STATIC_INLINE void
expand(HashTable *table, HashFunction f)
{
    int oldsegment;
    int oldindex;
    int newbucket;
    int newsegment;
    int newindex;
    HashList *hl;
    HashList *next;
    HashList *old, *new;

    if (table->split + table->max >= HDIRSIZE * HSEGSIZE)
        /* Wow!  That's big.  Too big, so don't expand. */
        return;

    /* Calculate indices of bucket to split */
    oldsegment = table->split / HSEGSIZE;
    oldindex = table->split % HSEGSIZE;

    newbucket = table->max + table->split;

    /* And the indices of the new bucket */
    newsegment = newbucket / HSEGSIZE;
    newindex = newbucket % HSEGSIZE;

    if (newindex == 0)
        allocSegment(table, newsegment);

    // A custom hash function may inspect the table during the split.
    table->dir[newsegment][newindex] = NULL;

    if (++table->split == table->max) {
        table->split = 0;
        table->max *= 2;
        table->mask1 = table->mask2;
        table->mask2 = table->mask2 << 1 | 1;
    }
    table->bcount++;

    /* Split the bucket, paying no attention to the original order */

    old = new = NULL;
    for (hl = table->dir[oldsegment][oldindex]; hl != NULL; hl = next) {
        next = hl->next;
        if (f(table, hl->key) == newbucket) {
            hl->next = new;
            new = hl;
        } else {
            hl->next = old;
            old = hl;
        }
    }
    table->dir[oldsegment][oldindex] = old;
    table->dir[newsegment][newindex] = new;

    return;
}
#endif

#if !defined(USE_RUST_RTS)
STATIC_INLINE void*
lookupHashTable_inlined(const HashTable *table, StgWord key,
                        HashFunction f, CompareFunction cmp)
{
    int bucket;
    int segment;
    int index;

    HashList *hl;

    bucket = f(table, key);
    segment = bucket / HSEGSIZE;
    index = bucket % HSEGSIZE;

    for (hl = table->dir[segment][index]; hl != NULL; hl = hl->next) {
        if (cmp(hl->key, key))
            return (void *) hl->data;
    }

    /* It's not there */
    return NULL;
}

#endif

void *
lookupHashTable_(const HashTable *table, StgWord key,
                 HashFunction f, CompareFunction cmp)
{
#if defined(USE_RUST_RTS)
    return (void *)ghc_rust_hash_lookup_custom(table, key, f, cmp);
#else
    return lookupHashTable_inlined(table, key, f, cmp);
#endif
}

void *
lookupHashTable(const HashTable *table, StgWord key)
{
#if defined(USE_RUST_RTS)
    return (void *)ghc_rust_hash_lookup_word(table, key);
#else
    return lookupHashTable_inlined(table, key, hashWord, compareWord);
#endif
}

void *
lookupStrHashTable(const StrHashTable* table, const char* key)
{
#if defined(USE_RUST_RTS)
    return (void *)ghc_rust_hash_lookup_str((const HashTable *)table, (StgWord)key);
#else
    return lookupHashTable_inlined(&table->table, (StgWord) key,
                                   hashStr, compareStr);
#endif
}

// Puts up to szKeys keys of the hash table into the given array. Returns the
// actual amount of keys that have been retrieved.
//
// If the table is modified concurrently, the function behavior is undefined.
//
int keysHashTable(HashTable *table, StgWord keys[], int szKeys) {
#if defined(USE_RUST_RTS)
    return ghc_rust_hash_keys(table, keys, szKeys);
#else
    int segment, index;
    int k = 0;
    HashList *hl;


    /* The last bucket with something in it is table->max + table->split - 1 */
    segment = (table->max + table->split - 1) / HSEGSIZE;
    index = (table->max + table->split - 1) % HSEGSIZE;

    while (segment >= 0 && k < szKeys) {
        while (index >= 0 && k < szKeys) {
            hl = table->dir[segment][index];
            while (hl && k < szKeys) {
                keys[k] = hl->key;
                k += 1;
                hl = hl->next;
            }
            index--;
        }
        segment--;
        index = HSEGSIZE - 1;
    }
    return k;
#endif
}

/* -----------------------------------------------------------------------------
 * We allocate the hashlist cells in large chunks to cut down on malloc
 * overhead.  Although we keep a free list of hashlist cells, we make
 * no effort to actually return the space to the malloc arena. Eventually
 * they will all be freed when we free the HashListChunks.
 * -------------------------------------------------------------------------- */

#if !defined(USE_RUST_RTS)
static HashList *
allocHashList (HashTable *table)
{
    if (table->freeList != NULL) {
        HashList *hl = table->freeList;
        table->freeList = hl->next;
        return hl;
    } else {
        /* We allocate one block of memory which contains:
         *
         *  1. A HashListChunk, which gets linked onto HashTable.chunks.
         *     This forms a list of all chunks associated with the HashTable
         *     and is what we will free when we free the HashTable.
         *
         *  2. Several HashLists. One of these will get returned. The rest are
         *     placed on the freeList.
         *
         */
        HashListChunk *cl = stgMallocBytes(sizeof(HashListChunk) + HCHUNK * sizeof(HashList), "allocHashList");
        HashList *hl = (HashList *) &cl[1];
        cl->next = table->chunks;
        table->chunks = cl;

        table->freeList = hl + 1;
        HashList *p = table->freeList;
        for (; p < hl + HCHUNK - 1; p++)
            p->next = p + 1;
        p->next = NULL;
        return hl;
    }
}

static void
freeHashList (HashTable *table, HashList *hl)
{
    // We place the HashList on the freeList. We make no attempt to bound the
    // size of the free list for the time being. The HashLists on the freeList
    // are freed when the HashTable itself is freed as a result of freeing the
    // HashListChunks.
    hl->next = table->freeList;
    table->freeList = hl;
}

STATIC_INLINE void
insertHashTable_inlined(HashTable *table, StgWord key,
                        const void *data, HashFunction f)
{
    int bucket;
    int segment;
    int index;
    HashList *hl;

    // Disable this assert; sometimes it's useful to be able to
    // overwrite entries in the hash table.
    // ASSERT(lookupHashTable(table, key) == NULL);

    if (table->kcount == INT_MAX) {
        barf("insertHashTable: too many entries");
    }

    /* When the average load gets too high, we expand the table */
    if (++table->kcount >= HLOAD * table->bcount)
        expand(table, f);

    bucket = f(table, key);
    segment = bucket / HSEGSIZE;
    index = bucket % HSEGSIZE;

    hl = allocHashList(table);

    hl->key = key;
    hl->data = data;
    hl->next = table->dir[segment][index];
    table->dir[segment][index] = hl;
}
#endif

void
insertHashTable_(HashTable *table, StgWord key,
                 const void *data, HashFunction f)
{
#if defined(USE_RUST_RTS)
    ghc_rust_hash_insert_custom(table, key, data, f);
#else
    insertHashTable_inlined(table, key, data, f);
#endif
}

void
insertHashTable(HashTable *table, StgWord key, const void *data)
{
#if defined(USE_RUST_RTS)
    ghc_rust_hash_insert_word(table, key, data);
#else
    insertHashTable_inlined(table, key, data, hashWord);
#endif
}

void
insertStrHashTable(StrHashTable *table, const char * key, const void *data)
{
#if defined(USE_RUST_RTS)
    ghc_rust_hash_insert_str((HashTable *)table, (StgWord)key, data);
#else
    insertHashTable_inlined(&table->table, (StgWord) key, data, hashStr);
#endif
}

#if defined(USE_RUST_RTS)
STATIC_INLINE void *finishHashRemoval(const void *result, const void *data STG_UNUSED)
{
    ASSERT(result != NULL || data == NULL);
    return (void *)result;
}
#else
STATIC_INLINE void*
removeHashTable_inlined(HashTable *table, StgWord key, const void *data,
                        HashFunction f, CompareFunction cmp)
{
    int bucket;
    int segment;
    int index;
    HashList *hl;
    HashList *prev = NULL;

    bucket = f(table, key);
    segment = bucket / HSEGSIZE;
    index = bucket % HSEGSIZE;

    for (hl = table->dir[segment][index]; hl != NULL; hl = hl->next) {
        if (cmp(hl->key, key) && (data == NULL || hl->data == data)) {
            if (prev == NULL)
                table->dir[segment][index] = hl->next;
            else
                prev->next = hl->next;
            freeHashList(table,hl);
            table->kcount--;
            return (void *) hl->data;
        }
        prev = hl;
    }

    /* It's not there */
    ASSERT(data == NULL);
    return NULL;
}

#endif

void*
removeHashTable_(HashTable *table, StgWord key, const void *data,
                 HashFunction f, CompareFunction cmp)
{
#if defined(USE_RUST_RTS)
    const void *result = ghc_rust_hash_remove_custom(table, key, data, f, cmp);
    return finishHashRemoval(result, data);
#else
    return removeHashTable_inlined(table, key, data, f, cmp);
#endif
}

void *
removeHashTable(HashTable *table, StgWord key, const void *data)
{
#if defined(USE_RUST_RTS)
    const void *result = ghc_rust_hash_remove_word(table, key, data);
    return finishHashRemoval(result, data);
#else
    return removeHashTable_inlined(table, key, data, hashWord, compareWord);
#endif
}

void *
removeStrHashTable(StrHashTable *table, const char * key, const void *data)
{
#if defined(USE_RUST_RTS)
    const void *result = ghc_rust_hash_remove_str((HashTable *)table, (StgWord)key, data);
    return finishHashRemoval(result, data);
#else
    return removeHashTable_inlined(&table->table, (StgWord) key,
                                   data, hashStr, compareStr);
#endif
}

/* -----------------------------------------------------------------------------
 * When we free a hash table, we are also good enough to free the
 * data part of each (key, data) pair, as long as our caller can tell
 * us how to do it.
 * -------------------------------------------------------------------------- */

void
freeHashTable(HashTable *table, void (*freeDataFun)(void *) )
{
#if defined(USE_RUST_RTS)
    ghc_rust_hash_free(table, freeDataFun);
#else
    /* The last bucket with something in it is table->max + table->split - 1 */
    long segment = (table->max + table->split - 1) / HSEGSIZE;
    long index = (table->max + table->split - 1) % HSEGSIZE;

    /* Free table segments */
    while (segment >= 0) {
        if (freeDataFun) {
            while (index >= 0) {
                HashList *next;
                for (HashList *hl = table->dir[segment][index]; hl != NULL; hl = next) {
                    next = hl->next;
                    (*freeDataFun)((void *) hl->data);
                }
                index--;
            }
        }
        stgFree(table->dir[segment]);
        segment--;
        index = HSEGSIZE - 1;
    }

    /* Free chunks */
    HashListChunk *cl = table->chunks;
    while (cl != NULL) {
        HashListChunk *old = cl;
        cl = cl->next;
        stgFree(old);
    }

    stgFree(table);
#endif
}

/* -----------------------------------------------------------------------------
 * Map a function over all the keys/values in a HashTable
 * -------------------------------------------------------------------------- */

void
mapHashTable(HashTable *table, void *data, MapHashFn fn)
{
#if defined(USE_RUST_RTS)
    ghc_rust_hash_map(table, data, fn);
#else
    /* The last bucket with something in it is table->max + table->split - 1 */
    long segment = (table->max + table->split - 1) / HSEGSIZE;
    long index = (table->max + table->split - 1) % HSEGSIZE;

    while (segment >= 0) {
        while (index >= 0) {
            for (HashList *hl = table->dir[segment][index]; hl != NULL; hl = hl->next) {
                fn(data, hl->key, hl->data);
            }
            index--;
        }
        segment--;
        index = HSEGSIZE - 1;
    }
#endif
}

void
mapHashTableKeys(HashTable *table, void *data, MapHashFnKeys fn)
{
#if defined(USE_RUST_RTS)
    ghc_rust_hash_map_keys(table, data, fn);
#else
    /* The last bucket with something in it is table->max + table->split - 1 */
    long segment = (table->max + table->split - 1) / HSEGSIZE;
    long index = (table->max + table->split - 1) % HSEGSIZE;

    while (segment >= 0) {
        while (index >= 0) {
            for (HashList *hl = table->dir[segment][index]; hl != NULL; hl = hl->next) {
                fn(data, &hl->key, hl->data);
            }
            index--;
        }
        segment--;
        index = HSEGSIZE - 1;
    }
#endif
}

void
iterHashTable(HashTable *table, void *data, IterHashFn fn)
{
#if defined(USE_RUST_RTS)
    ghc_rust_hash_iter(table, data, fn);
#else
    /* The last bucket with something in it is table->max + table->split - 1 */
    long segment = (table->max + table->split - 1) / HSEGSIZE;
    long index = (table->max + table->split - 1) % HSEGSIZE;

    while (segment >= 0) {
        while (index >= 0) {
            for (HashList *hl = table->dir[segment][index]; hl != NULL; hl = hl->next) {
                if (!fn(data, hl->key, hl->data)) {
                    return;
                }
            }
            index--;
        }
        segment--;
        index = HSEGSIZE - 1;
    }
#endif
}

/* -----------------------------------------------------------------------------
 * When we initialize a hash table, we set up the first segment as well,
 * initializing all of the first segment's hash buckets to NULL.
 * -------------------------------------------------------------------------- */

HashTable *
allocHashTable(void)
{
#if defined(USE_RUST_RTS)
    return ghc_rust_hash_alloc();
#else
    HashTable *table;
    HashList **hb;

    table = stgMallocBytes(sizeof(HashTable),"allocHashTable");

    allocSegment(table, 0);

    for (hb = table->dir[0]; hb < table->dir[0] + HSEGSIZE; hb++)
        *hb = NULL;

    table->split = 0;
    table->max = HSEGSIZE;
    table->mask1 = HSEGSIZE - 1;
    table->mask2 = 2 * HSEGSIZE - 1;
    table->kcount = 0;
    table->bcount = HSEGSIZE;
    table->freeList = NULL;
    table->chunks = NULL;

    return table;
#endif
}

int keyCountHashTable (HashTable *table)
{
#if defined(USE_RUST_RTS)
    return ghc_rust_hash_count(table);
#else
    return table->kcount;
#endif
}
