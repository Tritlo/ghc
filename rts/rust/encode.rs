use core::ffi::c_int;

// See Note [Floating-point environment for encoders] in StgPrimFloat.c.
unsafe extern "C" {
    fn ldexp(value: f64, exponent: c_int) -> f64;
    fn ghc_rust_encode_to_double(value: usize, signed: bool) -> f64;
    fn ghc_rust_encode_to_float_as_double(value: usize, signed: bool) -> f64;
    fn ghc_rust_encode_narrow(value: f64) -> f32;
}

fn scale(value: f64, magnitude: usize, exponent: isize) -> f64 {
    if magnitude == 0 {
        return value;
    }
    let exponent = exponent.clamp(c_int::MIN as isize, c_int::MAX as isize) as c_int;
    // Preserve the native libm contract, including errno and range exceptions.
    unsafe { ldexp(value, exponent) }
}

fn encode_double(magnitude: usize, exponent: isize, signed: bool) -> f64 {
    let value = unsafe { ghc_rust_encode_to_double(magnitude, signed) };
    scale(value, magnitude, exponent)
}

fn encode_float(magnitude: usize, exponent: isize, signed: bool) -> f32 {
    // Round the integer to Float, scale in Double, then narrow.
    let value = unsafe { ghc_rust_encode_to_float_as_double(magnitude, signed) };
    unsafe { ghc_rust_encode_narrow(scale(value, magnitude, exponent)) }
}

/// Scale an unsigned word to a Double with the RTS exponent range.
#[unsafe(no_mangle)]
pub(super) extern "C" fn ghc_rust_word_encode_double(value: usize, exponent: isize) -> f64 {
    encode_double(value, exponent, false)
}

/// Scale a signed word to a Double without overflowing its magnitude.
#[unsafe(no_mangle)]
pub(super) extern "C" fn ghc_rust_int_encode_double(value: isize, exponent: isize) -> f64 {
    let magnitude = value.unsigned_abs();
    let result = encode_double(magnitude, exponent, magnitude <= isize::MAX as usize);
    if value < 0 { -result } else { result }
}

/// Scale a word after rounding its magnitude to a Float.
#[unsafe(no_mangle)]
pub(super) extern "C" fn ghc_rust_word_encode_float(value: usize, exponent: isize) -> f32 {
    encode_float(value, exponent, false)
}

/// Scale a signed magnitude and preserve the sign of underflow.
#[unsafe(no_mangle)]
pub(super) extern "C" fn ghc_rust_int_encode_float(value: isize, exponent: isize) -> f32 {
    let magnitude = value.unsigned_abs();
    let result = encode_float(magnitude, exponent, magnitude <= isize::MAX as usize);
    if value < 0 { -result } else { result }
}
