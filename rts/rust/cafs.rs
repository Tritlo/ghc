use core::ffi::c_void;
use core::ptr;

core::arch::global_asm!(".hidden ghc_rust_mark_cafs", ".hidden ghc_rust_revert_cafs");

// GCAux.c checks these fields and the two static-link tag bits.
const STATIC_BITS: usize = 3;

#[repr(C)]
struct CafPayload {
    indirectee: *mut u8,
    static_link: *mut u8,
    saved_info: *const u8,
}

unsafe extern "C" {
    static mut dyn_caf_list: *mut u8;
    static mut revertible_caf_list: *mut u8;
    static mut unload_mark_needed: bool;
    fn markObjectCode(caf: *const u8);
}

// See Note [CAF lists] in sm/Storage.h and Note [Object unloading] in CheckUnload.c.
#[unsafe(no_mangle)]
unsafe extern "C" fn ghc_rust_mark_cafs(
    evac: unsafe extern "C" fn(*mut c_void, *mut *mut u8),
    user: *mut c_void,
    payload_offset: usize,
) {
    unsafe {
        for head in [&raw const dyn_caf_list, &raw const revertible_caf_list] {
            let mut link = head.read();
            loop {
                let caf = link.map_addr(|addr| addr & !STATIC_BITS);
                if caf.is_null() {
                    break;
                }
                let payload = caf.add(payload_offset).cast::<CafPayload>();
                evac(user, &raw mut (*payload).indirectee);
                if unload_mark_needed {
                    markObjectCode(caf);
                }
                link = (*payload).static_link;
            }
        }
    }
}

#[unsafe(no_mangle)]
unsafe extern "C" fn ghc_rust_revert_cafs(payload_offset: usize) {
    unsafe {
        let end = ptr::without_provenance_mut(STATIC_BITS);
        let mut link = revertible_caf_list;
        while link != end {
            let caf = link.map_addr(|addr| addr & !STATIC_BITS);
            let payload = caf.add(payload_offset).cast::<CafPayload>();
            link = (*payload).static_link;
            caf.cast::<*const u8>().write((*payload).saved_info);
            (*payload).saved_info = ptr::null();
            // Clear the tag so a later major GC can visit this CAF again (#16842).
            (*payload).static_link = ptr::null_mut();
        }
        revertible_caf_list = end;
    }
}
