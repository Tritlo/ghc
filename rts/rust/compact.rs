use super::COMPACT_BLOCK_NEXT;

core::arch::global_asm!(".hidden ghc_rust_free_compact_blocks");

unsafe extern "C" {
    fn ghc_c_free_compact_block(block: *mut u8);
}

/// Free each block in a compact region while the caller owns SM_LOCK.
#[unsafe(no_mangle)]
unsafe extern "C" fn ghc_rust_free_compact_blocks(mut block: *mut u8) {
    unsafe {
        while !block.is_null() {
            let next = block.add(COMPACT_BLOCK_NEXT).cast::<*mut u8>().read();
            ghc_c_free_compact_block(block);
            block = next;
        }
    }
}
