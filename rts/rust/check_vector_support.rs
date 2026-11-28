#![no_std]

use core::arch::x86_64::{__cpuid, __cpuid_count, _xgetbv};
use core::ffi::c_int;

const SSE: u32 = 1 << 25;
const OSXSAVE: u32 = 1 << 27;
const AVX: u32 = 1 << 28;
const AVX2: u32 = 1 << 5;
const AVX512F: u32 = 1 << 16;

// See Note [Vector state availability] in rts/CheckVectorSupportInternal.h.
fn classify_vector_support(leaf1_ecx: u32, leaf1_edx: u32, leaf7_ebx: u32, xcr0: u64) -> c_int {
    let supports_v16 = leaf1_edx & SSE != 0;
    let supports_avx = leaf1_ecx & (OSXSAVE | AVX) == OSXSAVE | AVX && xcr0 & 0x6 == 0x6;
    let supports_v32 = supports_avx && leaf7_ebx & AVX2 != 0;
    let supports_v64 = supports_avx && xcr0 & 0xe0 == 0xe0 && leaf7_ebx & AVX512F != 0;

    if supports_v64 {
        3
    } else if supports_v32 {
        2
    } else if supports_v16 {
        1
    } else {
        0
    }
}

#[unsafe(export_name = "vectorSupportGlobalVar")]
pub static mut VECTOR_SUPPORT_GLOBAL: c_int = 0;

/* Note [Vector support symbol preemption]
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * The dynamic RTS calls checkVectorSupport through its public symbol.
 * It writes vectorSupportGlobalVar through its public symbol.
 * Keep the detector out of setVectorSupport so the linker can replace it.
 */
#[unsafe(export_name = "checkVectorSupport")]
#[inline(never)]
pub extern "C" fn check_vector_support() -> c_int {
    // SAFETY: CPUID is available on x86_64. XGETBV is executed only when CPUID
    // reports OSXSAVE, which states that the operating system supports it.
    unsafe {
        let max_basic_leaf = __cpuid(0).eax;
        let leaf1 = __cpuid(1);
        let leaf7_ebx = if max_basic_leaf >= 7 {
            __cpuid_count(7, 0).ebx
        } else {
            0
        };
        let xcr0 = if leaf1.ecx & OSXSAVE != 0 {
            _xgetbv(0)
        } else {
            0
        };
        classify_vector_support(leaf1.ecx, leaf1.edx, leaf7_ebx, xcr0)
    }
}

#[unsafe(export_name = "setVectorSupport")]
pub extern "C" fn set_vector_support() {
    // SAFETY: RTS startup calls this before threads read vectorSupportGlobalVar.
    unsafe {
        VECTOR_SUPPORT_GLOBAL = check_vector_support();
    }
}
