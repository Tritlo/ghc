core::arch::global_asm!(".hidden ghc_rust_count_blocks");

// BlockAlloc.c supplies the descriptor offsets and megablock geometry.
// See Note [Counting allocated blocks] in BlockAlloc.c.
#[unsafe(no_mangle)]
unsafe extern "C" fn ghc_rust_count_blocks(
    mut bd: *const u8,
    link_offset: usize,
    blocks_offset: usize,
    megablock_shift: usize,
    descriptor_blocks: usize,
) -> usize {
    let mut count = 0usize;
    while !bd.is_null() {
        let blocks = unsafe { bd.add(blocks_offset).cast::<u32>().read() as usize };
        let correction = descriptor_blocks.wrapping_mul(blocks >> megablock_shift);
        count = count.wrapping_add(blocks).wrapping_sub(correction);
        bd = unsafe { bd.add(link_offset).cast::<*const u8>().read() };
    }
    count
}
