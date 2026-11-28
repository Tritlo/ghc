use core::ffi::c_void;
use core::mem::size_of;
use core::ptr;

core::arch::global_asm!(".hidden ghc_rust_clone_stack");

#[repr(C)]
struct CloneStackLayout {
    stack_size_offset: usize,
    dirty_offset: usize,
    sp_offset: usize,
    stack_offset: usize,
    underflow_bytes: usize,
    underflow_info_offset: usize,
    underflow_next_offset: usize,
    underflow_info: [*const c_void; 4],
    check: Option<unsafe extern "C" fn(*const c_void) -> usize>,
}

unsafe extern "C" {
    fn allocate(capability: *mut c_void, words: usize) -> *mut u8;
}

// Note [Stack snapshot layout]
// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
// CloneStack.c supplies field offsets and frame labels for each RTS way.
// Keep the source and clone as raw pointers during native allocation.
// Copy the complete closure, including unused stack words.
unsafe fn clone_chunk(
    capability: *mut c_void,
    source: *const u8,
    layout: &CloneStackLayout,
) -> *mut u8 {
    unsafe {
        let word = size_of::<usize>();
        let stack_size = source.add(layout.stack_size_offset).cast::<u32>().read() as usize;
        let source_stack = source.add(layout.stack_offset);
        let source_sp = source.add(layout.sp_offset).cast::<*const u8>().read();
        let sp_offset_bytes = source_sp.addr() - source_stack.addr();
        let bytes = layout.stack_offset + stack_size * word;
        let cloned = allocate(capability, bytes.div_ceil(word));
        ptr::copy_nonoverlapping(source, cloned, bytes);
        cloned
            .add(layout.sp_offset)
            .cast::<*mut u8>()
            .write(cloned.add(layout.stack_offset + sp_offset_bytes));
        cloned.add(layout.dirty_offset).write(0);
        if let Some(check) = layout.check {
            let _ = check(cloned.cast());
        }
        cloned
    }
}

#[unsafe(no_mangle)]
unsafe extern "C" fn ghc_rust_clone_stack(
    capability: *mut c_void,
    source: *const u8,
    layout: &CloneStackLayout,
) -> *mut u8 {
    unsafe {
        let top = clone_chunk(capability, source, layout);
        let mut last = top;
        let word = size_of::<usize>();
        loop {
            let stack_size = last.add(layout.stack_size_offset).cast::<u32>().read() as usize;
            let end = last.add(layout.stack_offset + stack_size * word);
            let sp = last.add(layout.sp_offset).cast::<*const u8>().read();
            if end.addr() - sp.addr() < layout.underflow_bytes {
                break;
            }
            let frame = end.sub(layout.underflow_bytes);
            let info = frame
                .add(layout.underflow_info_offset)
                .cast::<*const c_void>()
                .read();
            if !layout.underflow_info.contains(&info) {
                break;
            }
            let next_source = frame
                .add(layout.underflow_next_offset)
                .cast::<*const u8>()
                .read();
            let next = clone_chunk(capability, next_source, layout);
            frame
                .add(layout.underflow_next_offset)
                .cast::<*mut u8>()
                .write(next);
            last = next;
        }
        top
    }
}
