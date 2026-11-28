use core::sync::atomic::{AtomicU8, Ordering};

core::arch::global_asm!(".hidden ghc_rust_count_nonmoving_marks");

#[inline]
unsafe fn count(marks: *const AtomicU8, n: u32, live: impl Fn(u8) -> bool) -> u32 {
    let mut total = 0;
    for i in 0..n {
        let mark = unsafe { (*marks.add(i as usize)).load(Ordering::Relaxed) };
        total += u32::from(live(mark));
    }
    total
}

// The current segment can contain allocations from either mark epoch.
// Active segments contribute only blocks marked in the current epoch.
#[unsafe(no_mangle)]
unsafe extern "C" fn ghc_rust_count_nonmoving_marks(
    marks: *const AtomicU8,
    n: u32,
    epoch: u8,
) -> u32 {
    if epoch == 0 {
        unsafe { count(marks, n, |mark| mark != 0) }
    } else {
        unsafe { count(marks, n, |mark| mark == epoch) }
    }
}
