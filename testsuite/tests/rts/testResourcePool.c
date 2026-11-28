#include "Pool.h"

#include <stdio.h>
#include <stdlib.h>

static int resource;
static unsigned releases;
static bool fail_next;
static Pool *pool;

static void *acquire(void)
{
    if (poolGetMaxSize(pool) != 1) abort();
    if (fail_next) {
        fail_next = false;
        return NULL;
    }
    return &resource;
}

static void release(void *value)
{
    if (poolGetDesiredSize(pool) > 1) abort();
    if (value != &resource) abort();
    releases++;
}

static void expect(bool ok, const char *message)
{
    if (!ok) {
        fprintf(stderr, "%s\n", message);
        exit(EXIT_FAILURE);
    }
}

int main(int argc, char **argv)
{
    hs_init(&argc, &argv);
    pool = poolInit(1, 1, acquire, release);
    void *value = poolTake(pool);
    expect(value == &resource && poolFree(pool) == 1, "busy pool destruction");
    poolRelease(pool, value);
    expect(releases == 0, "cached resource released too early");
    expect(poolFree(pool) == 0 && releases == 1, "cached resource leaked");

    pool = poolInit(1, 0, acquire, release);
    value = poolTake(pool);
    poolRelease(pool, value);
    expect(releases == 2, "idle size zero retained a resource");
    value = poolTryTake(pool);
    expect(value == &resource, "returned resource still counts towards capacity");
    poolRelease(pool, value);
    expect(poolFree(pool) == 0 && releases == 3, "unused capacity pool cleanup");

    pool = poolInit(1, 1, acquire, release);
    fail_next = true;
    expect(poolTake(pool) == NULL, "allocation failure not returned");
    value = poolTryTake(pool);
    expect(value == &resource, "allocation failure consumed capacity");
    poolFlush(pool);
    poolRelease(pool, value);
    expect(releases == 4, "flushed resource retained after return");
    value = poolTryTake(pool);
    expect(value == &resource, "flushed resource still counts towards capacity");
    poolRelease(pool, value);
    expect(poolFree(pool) == 0 && releases == 5, "final pool cleanup");
    hs_exit();
    return 0;
}
