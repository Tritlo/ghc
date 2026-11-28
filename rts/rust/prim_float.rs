/// Decode an IEEE binary32 value into GHC's signed mantissa and exponent.
///
/// # Safety
///
/// Both output pointers must be aligned and valid for writes of one RTS word.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn ghc_rust_decode_float_int(
    mantissa: *mut isize,
    exponent: *mut isize,
    value: f32,
) {
    let bits = value.to_bits();
    let fraction = bits & 0x007f_ffff;
    let biased_exponent = ((bits >> 23) & 0xff) as isize;

    let (unsigned_mantissa, decoded_exponent) = match (biased_exponent, fraction) {
        (0, 0) => (0, 0),
        (0, _) => {
            // Shift the leading bit of a subnormal fraction to bit 23.
            let shift = fraction.leading_zeros() - 8;
            (fraction << shift, -149 - shift as isize)
        }
        _ => (fraction | 0x0080_0000, biased_exponent - 150),
    };
    let signed_mantissa = if bits >> 31 == 0 {
        unsigned_mantissa as isize
    } else {
        -(unsigned_mantissa as isize)
    };

    unsafe {
        mantissa.write(signed_mantissa);
        exponent.write(decoded_exponent);
    }
}

/// Decode binary64 bits. Preserve the significand bits of infinities and NaNs,
/// as required by GHC's floating-point primops.
fn decode_double(value: f64) -> (i64, isize) {
    let bits = value.to_bits();
    let fraction = bits & 0x000f_ffff_ffff_ffff;
    let biased = ((bits >> 52) & 0x7ff) as isize;
    let (magnitude, exponent) = match (biased, fraction) {
        (0, 0) => return (0, 0),
        (0, _) => {
            let shift = fraction.leading_zeros() - 11;
            (fraction << shift, -1074 - shift as isize)
        }
        _ => (fraction | (1 << 52), biased - 1075),
    };
    let mantissa = magnitude as i64;
    (if bits >> 63 == 0 { mantissa } else { -mantissa }, exponent)
}

/// Write the signed Double mantissa and return its exponent.
///
/// # Safety
///
/// The caller must provide storage for eight bytes on the STG stack.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn ghc_rust_decode_double_int64(output: *mut i64, value: f64) -> isize {
    let (mantissa, exponent) = decode_double(value);
    unsafe { output.write_unaligned(mantissa) };
    exponent
}

/// Write the sign, two halves of the mantissa, and exponent of a Double.
///
/// # Safety
///
/// The output pointers must refer to distinct, writable, aligned RTS words.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn ghc_rust_decode_double_2int(
    sign: *mut isize,
    high: *mut usize,
    low: *mut usize,
    exponent: *mut isize,
    value: f64,
) {
    let (mantissa, decoded_exponent) = decode_double(value);
    let magnitude = mantissa.unsigned_abs();
    unsafe {
        // The split-word ABI leaves the sign slot untouched for either zero.
        if mantissa != 0 {
            sign.write(mantissa.signum() as isize);
        }
        high.write((magnitude >> 32) as usize);
        low.write(magnitude as u32 as usize);
        exponent.write(decoded_exponent);
    }
}
