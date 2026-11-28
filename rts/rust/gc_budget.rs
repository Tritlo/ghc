use core::num::{NonZeroUsize, Wrapping};

/// Limit the old-generation size for a finite heap.
///
/// The C caller checks heap overflow before and after this calculation.
///
/// # Safety
///
/// The generation count must be between 2 and the RTS limit of 64.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_limit_generation_size(
    size: usize,
    max_heap: usize,
    min_alloc: usize,
    generations: usize,
    in_place_oldest: bool,
) -> usize {
    // Keep unsigned RTS word arithmetic even if the caller set heap overflow.
    let size = Wrapping(size);
    let max_heap = Wrapping(max_heap);
    let min_alloc = Wrapping(min_alloc);
    let generations = Wrapping(generations);
    let copying_units = (generations - Wrapping(1)) * Wrapping(2);
    let (required, units) = if in_place_oldest {
        (
            size + (size - Wrapping(1)) * (generations - Wrapping(2)) * Wrapping(2),
            copying_units - Wrapping(1),
        )
    } else {
        (size * copying_units, copying_units)
    };

    if required + min_alloc <= max_heap {
        return size.0;
    }

    // With 2 to 64 generations, units is at least 1 and at most 126.
    let units = unsafe { NonZeroUsize::new_unchecked(units.0) };
    (max_heap - min_alloc).0 / units
}
