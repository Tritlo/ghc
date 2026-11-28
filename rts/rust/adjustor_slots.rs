use core::arch::global_asm;

global_asm!(
    ".hidden ghc_rust_adjustor_claim_slot",
    ".hidden ghc_rust_adjustor_return_slot",
);

/// Claim the first free slot and find the next free slot.
/// The caller holds the pool lock and provides a bitmap with `chunk_slots` bits.
/// `first_free` must name an unset bit within that bitmap.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_adjustor_claim_slot(
    bitmap: *mut u8,
    first_free: *mut usize,
    chunk_slots: usize,
) -> usize {
    unsafe {
        let slot = *first_free;
        *bitmap.add(slot / 8) |= 1u8 << (slot % 8);

        let mut next = slot + 1;
        while next < chunk_slots {
            if *bitmap.add(next / 8) & (1u8 << (next % 8)) == 0 {
                break;
            }
            next += 1;
        }
        *first_free = next;
        slot
    }
}

/// Return a claimed slot and update the first free slot.
/// The caller holds the pool lock and provides a claimed slot in the bitmap.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_adjustor_return_slot(
    bitmap: *mut u8,
    first_free: *mut usize,
    slot: usize,
) {
    unsafe {
        *bitmap.add(slot / 8) &= !(1u8 << (slot % 8));
        if slot < *first_free {
            *first_free = slot;
        }
    }
}
