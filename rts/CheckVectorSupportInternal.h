#pragma once

/*
Note [Vector state availability]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
CPUID reports the vector features that the CPU implements. The OSXSAVE bit
states that the operating system supports XGETBV. XCR0 then states which
register state the operating system saves and restores. Read XCR0 only when
OSXSAVE is set. Select a vector width only when XCR0 enables all state that
instructions of that width can use.
*/
static inline int
classifyVectorSupport(unsigned int leaf1_ecx, unsigned int leaf1_edx,
                      unsigned int leaf7_ebx, unsigned long long xcr0)
{
    int supports_V16 = leaf1_edx & (1u << 25); // SSE
    int supports_AVX =
        (leaf1_ecx & ((1u << 27) | (1u << 28))) ==
            ((1u << 27) | (1u << 28)) && // OSXSAVE and AVX
        (xcr0 & 0x6) == 0x6;              // XMM and YMM state
    int supports_V32 = supports_AVX && (leaf7_ebx & (1u << 5)); // AVX2
    int supports_V64 =
        supports_AVX && (xcr0 & 0xe0) == 0xe0 && // opmask and ZMM state
        (leaf7_ebx & (1u << 16));                 // AVX-512F

    if (supports_V64) {
        return 3;
    }
    if (supports_V32) {
        return 2;
    }
    if (supports_V16) {
        return 1;
    }
    return 0;
}
