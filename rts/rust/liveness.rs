use core::ptr::null_mut;
use core::sync::atomic::{AtomicPtr, Ordering, fence};

core::arch::global_asm!(
    ".hidden ghc_rust_is_alive",
    ".hidden ghc_rust_is_alive_large"
);

// GCAux.c checks these values against the native RTS headers.
const TAG_MASK: usize = 7;
const BF_EVACUATED: u16 = 1;
const BF_LARGE: u16 = 2;
const BF_MARKED: u16 = 8;
const BF_NONMOVING: u16 = 1024;
const IND: u32 = 27;
const IND_STATIC: u32 = 28;
const BLACKHOLE: u32 = 38;

// Query liveness before compaction. Follow each indirection with its own tag.
#[unsafe(no_mangle)]
unsafe extern "C" fn ghc_rust_is_alive(
    pointer: *mut u8,
    block_flags: unsafe extern "C" fn(*mut u8) -> *const u16,
    marked: unsafe extern "C" fn(*mut u8) -> bool,
    info_type_offset: isize,
    indirectee_offset: usize,
) -> *mut u8 {
    unsafe {
        follow(
            pointer,
            |p| block_flags(p),
            |p, _| marked(p),
            info_type_offset,
            indirectee_offset,
        )
    }
}

#[repr(C)]
struct HeapRange {
    begin: usize,
    end: usize,
}

// See Note [Block lookup for closure liveness] in sm/GCAux.c.
#[unsafe(no_mangle)]
unsafe extern "C" fn ghc_rust_is_alive_large(pointer: *mut u8, range: &HeapRange) -> *mut u8 {
    const MEGABLOCK_MASK: usize = (1 << 20) - 1;
    const BLOCK_MASK: usize = (1 << 12) - 1;
    const FLAGS_OFFSET: usize = 46;
    const BITMAP_OFFSET: usize = 24;

    let flags = |closure: *mut u8| {
        let address = closure.addr();
        if address < range.begin || address >= range.end {
            return core::ptr::null();
        }
        let block_index = (address & MEGABLOCK_MASK & !BLOCK_MASK) >> 12;
        let descriptor = (address & !MEGABLOCK_MASK) + (block_index << 6);
        // The RTS stores the reserved heap range as exposed addresses.
        core::ptr::with_exposed_provenance(descriptor + FLAGS_OFFSET)
    };
    let marked = |closure: *mut u8, flags: *const u16| unsafe {
        let block = flags.cast::<u8>().sub(FLAGS_OFFSET);
        let start = block.cast::<*const usize>().read();
        let bitmap = block.add(BITMAP_OFFSET).cast::<*const usize>().read();
        let bit = (closure.addr() - start.addr()) / size_of::<usize>();
        let word = bitmap.add(bit / usize::BITS as usize).read();
        word & (1usize << (bit % usize::BITS as usize)) != 0
    };
    unsafe { follow(pointer, flags, marked, -8, 8) }
}

#[inline]
unsafe fn follow(
    mut pointer: *mut u8,
    block_flags: impl Fn(*mut u8) -> *const u16,
    marked: impl Fn(*mut u8, *const u16) -> bool,
    info_type_offset: isize,
    indirectee_offset: usize,
) -> *mut u8 {
    unsafe {
        loop {
            let closure = pointer.map_addr(|addr| addr & !TAG_MASK);
            let flags = block_flags(closure);
            if flags.is_null() {
                return pointer;
            }
            let bits = flags.read();
            if bits & (BF_NONMOVING | BF_EVACUATED) != 0 {
                return pointer;
            }
            if bits & BF_LARGE != 0 {
                return null_mut();
            }
            if bits & BF_MARKED != 0 && marked(closure, flags) {
                return pointer;
            }

            let info = AtomicPtr::<u8>::from_ptr(closure.cast()).load(Ordering::Relaxed);
            if info.addr() & 1 != 0 {
                return info.map_addr(|addr| (addr - 1) | (pointer.addr() & TAG_MASK));
            }
            fence(Ordering::Acquire);
            let kind = info.wrapping_offset(info_type_offset).cast::<u32>().read();
            match kind {
                IND | IND_STATIC | BLACKHOLE => {
                    pointer = closure.add(indirectee_offset).cast::<*mut u8>().read();
                    if kind == BLACKHOLE && pointer.addr() & TAG_MASK == 0 {
                        return null_mut();
                    }
                }
                _ => return null_mut(),
            }
        }
    }
}
