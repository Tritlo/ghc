use core::slice;

core::arch::global_asm!(".hidden ghc_rust_sweep_blocks");

// Sweep.c supplies the block descriptor field offsets and bitmap length.
#[repr(C)]
struct SweepLayout {
    link: usize,
    bitmap: usize,
    flags: usize,
    bitmap_words: usize,
}

#[repr(C)]
#[derive(Default)]
struct SweepStats {
    marked: usize,
    freed: usize,
    fragmented: usize,
    live: usize,
}

unsafe extern "C" {
    fn freeGroup(block: *mut u8);
}

// Note [Sweeping marked blocks]
// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
// The collector holds the storage manager lock. Count nonempty bitmap words
// to estimate live heap words. Unlink each empty block before the allocator
// takes it back. The allocator can overwrite the descriptor, including its link.
#[unsafe(no_mangle)]
unsafe extern "C" fn ghc_rust_sweep_blocks(
    mut slot: *mut *mut u8,
    count: *mut usize,
    layout: &SweepLayout,
) -> SweepStats {
    const BF_MARKED: u16 = 8;
    const BF_FRAGMENTED: u16 = 64;
    const BF_SWEPT: u16 = 256;
    let mut stats = SweepStats::default();
    unsafe {
        let mut block = slot.read();
        while !block.is_null() {
            let link = block.add(layout.link).cast::<*mut u8>();
            let next = link.read();
            let flags = block.add(layout.flags).cast::<u16>();
            let bits = flags.read();
            if bits & BF_MARKED != 0 {
                stats.marked += 1;
                let bitmap = block.add(layout.bitmap).cast::<*const usize>().read();
                let words = slice::from_raw_parts(bitmap, layout.bitmap_words);
                let occupied = words.iter().filter(|&&word| word != 0).count();
                if occupied == 0 {
                    stats.freed += 1;
                    *count -= 1;
                    slot.write(next);
                    freeGroup(block);
                    block = next;
                    continue;
                }
                stats.live += occupied * usize::BITS as usize;
                let mut survivor_flags = bits | BF_SWEPT;
                if occupied < layout.bitmap_words * 3 / 4 {
                    stats.fragmented += 1;
                    survivor_flags |= BF_FRAGMENTED;
                }
                flags.write(survivor_flags);
            }
            slot = link;
            block = next;
        }
    }
    stats
}
