#include "Rts.h"

extern Mutex sm_mutex;
extern bdescr *nonmoving_large_objects;
extern void nonmovingSweepLargeObjects(void);

enum { batch = 10000, count = 2 * batch + 1 };
static bdescr groups[count];
static unsigned freed, yields;

void __wrap_freeGroup(bdescr *bd)
{
    if (freed >= count || bd != &groups[freed]) {
        abort();
    }
    ++freed;
    bd->link = NULL;
}

void __wrap_yieldThread(void)
{
    ++yields;
    if (freed != yields * batch) {
        fprintf(stderr, "yield %u after %u groups\n", yields, freed);
        exit(1);
    }
    if (pthread_mutex_trylock(&sm_mutex) != 0) {
        abort();
    }
    pthread_mutex_unlock(&sm_mutex);
}

int main(void)
{
    // Use descriptors of different sizes. The budget counts groups.
    for (unsigned i = 0; i < count; ++i) {
        groups[i].blocks = 1 + i % 4;
        groups[i].link = i + 1 < count ? &groups[i + 1] : NULL;
    }
    initMutex(&sm_mutex);
    nonmoving_large_objects = groups;
    nonmovingSweepLargeObjects();
    closeMutex(&sm_mutex);
    return freed != count || yields != 2;
}
