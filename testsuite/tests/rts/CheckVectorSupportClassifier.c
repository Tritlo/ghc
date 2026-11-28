#include "CheckVectorSupportInternal.h"

enum {
    SSE = 1u << 25,
    OSXSAVE = 1u << 27,
    AVX = 1u << 28,
    AVX2 = 1u << 5,
    AVX512F = 1u << 16,
};

int main(void)
{
    if (classifyVectorSupport(0, 0, 0, 0) != 0) return 1;
    if (classifyVectorSupport(0, SSE, 0, 0) != 1) return 1;

    if (classifyVectorSupport(AVX, SSE, AVX2, 0) != 1) return 1;
    if (classifyVectorSupport(OSXSAVE, SSE, AVX2, 0x6) != 1) return 1;
    if (classifyVectorSupport(OSXSAVE | AVX, SSE, AVX2, 0x2) != 1) return 1;
    if (classifyVectorSupport(OSXSAVE | AVX, SSE, AVX2, 0x6) != 2) return 1;

    if (classifyVectorSupport(OSXSAVE | AVX, SSE, AVX512F, 0x6) != 1) return 1;
    if (classifyVectorSupport(OSXSAVE | AVX, SSE, AVX512F, 0xc6) != 1) return 1;
    if (classifyVectorSupport(OSXSAVE | AVX, SSE, AVX512F, 0xe6) != 3) return 1;
    return 0;
}
