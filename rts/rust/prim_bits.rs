#![no_std]

// The subword primops accept a full machine word. Narrow the operand before
// counting so that bits above the requested width do not affect the result.
macro_rules! bit_counts {
    ($argument:ty, $width:ty, $population:ident, $leading:ident, $trailing:ident) => {
        #[unsafe(no_mangle)]
        pub extern "C" fn $population(value: $argument) -> usize {
            (value as $width).count_ones() as usize
        }

        #[unsafe(no_mangle)]
        pub extern "C" fn $leading(value: $argument) -> usize {
            (value as $width).leading_zeros() as usize
        }

        #[unsafe(no_mangle)]
        pub extern "C" fn $trailing(value: $argument) -> usize {
            (value as $width).trailing_zeros() as usize
        }
    };
}

bit_counts!(usize, u8, hs_popcnt8, hs_clz8, hs_ctz8);
bit_counts!(usize, u16, hs_popcnt16, hs_clz16, hs_ctz16);
bit_counts!(usize, u32, hs_popcnt32, hs_clz32, hs_ctz32);
bit_counts!(u64, u64, hs_popcnt64, hs_clz64, hs_ctz64);

#[unsafe(no_mangle)]
pub extern "C" fn hs_popcnt(value: usize) -> usize {
    value.count_ones() as usize
}

macro_rules! transform {
    ($argument:ty, $width:ty, $name:ident, $method:ident) => {
        #[unsafe(no_mangle)]
        pub extern "C" fn $name(value: $argument) -> $argument {
            (value as $width).$method() as $argument
        }
    };
}

transform!(usize, u8, hs_bitrev8, reverse_bits);
transform!(usize, u16, hs_bitrev16, reverse_bits);
transform!(usize, u32, hs_bitrev32, reverse_bits);
transform!(u64, u64, hs_bitrev64, reverse_bits);

transform!(usize, u16, hs_bswap16, swap_bytes);
transform!(usize, u32, hs_bswap32, swap_bytes);
transform!(u64, u64, hs_bswap64, swap_bytes);

#[unsafe(no_mangle)]
pub extern "C" fn hs_mulIntMayOflo(a: usize, b: usize) -> usize {
    (a as isize).overflowing_mul(b as isize).1 as usize
}

fn deposit(mut value: u64, mut mask: u64) -> u64 {
    let mut result = 0;
    while mask != 0 {
        let lowest = mask & mask.wrapping_neg();
        result |= lowest & (value & 1).wrapping_neg();
        mask &= mask.wrapping_sub(1);
        value >>= 1;
    }
    result
}

fn extract(value: u64, mut mask: u64) -> u64 {
    let mut result = 0;
    let mut output = 1;
    while mask != 0 {
        let lowest = mask & mask.wrapping_neg();
        if value & lowest != 0 {
            result |= output;
        }
        mask &= mask.wrapping_sub(1);
        output <<= 1;
    }
    result
}

macro_rules! bit_permutation {
    ($argument:ty, $width:ty, $deposit:ident, $extract:ident) => {
        #[unsafe(no_mangle)]
        pub extern "C" fn $deposit(value: $argument, mask: $argument) -> $argument {
            deposit(value as $width as u64, mask as $width as u64) as $argument
        }

        #[unsafe(no_mangle)]
        pub extern "C" fn $extract(value: $argument, mask: $argument) -> $argument {
            let value = value as $width;
            let mask = mask as $width;
            if mask == <$width>::MAX {
                return value as $argument;
            }
            extract(value as u64, mask as u64) as $argument
        }
    };
}

bit_permutation!(usize, u8, hs_pdep8, hs_pext8);
bit_permutation!(usize, u16, hs_pdep16, hs_pext16);
bit_permutation!(usize, u32, hs_pdep32, hs_pext32);
bit_permutation!(u64, u64, hs_pdep64, hs_pext64);
