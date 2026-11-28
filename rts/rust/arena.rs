use core::ffi::{c_char, c_void};
use core::mem::{MaybeUninit, size_of};
use core::ptr::null_mut;

#[repr(C)]
struct Group {
    block: *mut c_void,
    start: *mut usize,
    limit: *mut usize,
}

// C uses an opaque Arena pointer. Rust does not access block descriptors.
struct Arena {
    block: *mut c_void,
    cursor: *mut usize,
    limit: *mut usize,
    max_size: usize,
}

unsafe extern "C" {
    fn stgMallocBytes(size: usize, label: *const c_char) -> *mut c_void;
    fn stgFree(ptr: *mut c_void);
    fn exitHeapOverflow() -> !;
    fn ghc_rust_arena_acquire(previous: *mut c_void, words: usize, out: *mut Group);
    fn ghc_rust_arena_release(block: *mut c_void) -> *mut c_void;
}

// This symbol is in the common object. Only debug C code refers to it.
core::arch::global_asm!(".hidden ghc_rust_arena_position");

fn acquire(previous: *mut c_void, words: usize) -> Group {
    let mut group = MaybeUninit::uninit();
    unsafe {
        ghc_rust_arena_acquire(previous, words, group.as_mut_ptr());
        group.assume_init()
    }
}

#[unsafe(no_mangle)]
unsafe extern "C" fn ghc_rust_new_arena(max_size: usize) -> *mut Arena {
    let state = unsafe { stgMallocBytes(size_of::<Arena>(), c"newArena".as_ptr()).cast::<Arena>() };
    let group = acquire(null_mut(), 0);
    unsafe {
        state.write(Arena {
            block: group.block,
            cursor: group.start,
            limit: group.limit,
            max_size,
        });
    }
    state
}

#[unsafe(no_mangle)]
unsafe extern "C" fn ghc_rust_arena_alloc(arena: *mut Arena, size: usize) -> *mut c_void {
    // The caller has exclusive access to this arena, as for the C allocator.
    let arena = unsafe { &mut *arena };
    if size > arena.max_size {
        unsafe { exitHeapOverflow() };
    }

    // The C bound is block-aligned and leaves room for rounding to eight bytes.
    const MIN_ALIGN: usize = 8;
    let bytes = (size + MIN_ALIGN - 1) & !(MIN_ALIGN - 1);
    let words = bytes / size_of::<usize>();
    let current = arena.cursor;
    let remaining = arena.limit.addr() - current.addr();

    // An exact fit starts a new group.
    if bytes < remaining {
        arena.cursor = unsafe { current.add(words) };
        return current.cast();
    }

    let group = acquire(arena.block, words);
    arena.block = group.block;
    arena.cursor = unsafe { group.start.add(words) };
    arena.limit = group.limit;
    group.start.cast()
}

#[unsafe(no_mangle)]
unsafe extern "C" fn ghc_rust_arena_free(arena: *mut Arena) {
    let mut block = unsafe { (*arena).block };
    while !block.is_null() {
        block = unsafe { ghc_rust_arena_release(block) };
    }
    unsafe { stgFree(arena.cast()) };
}

#[unsafe(no_mangle)]
unsafe extern "C" fn ghc_rust_arena_position(
    arena: *const Arena,
    cursor: *mut *mut usize,
) -> *mut c_void {
    let arena = unsafe { &*arena };
    unsafe { cursor.write(arena.cursor) };
    arena.block
}
