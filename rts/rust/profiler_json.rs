#![no_std]

use core::{mem::MaybeUninit, slice};

fn escape_byte(byte: u8) -> ([u8; 6], usize) {
    let short_escape = match byte {
        b'"' | b'\\' => byte,
        0x08 => b'b',
        0x0c => b'f',
        b'\n' => b'n',
        b'\r' => b'r',
        b'\t' => b't',
        0x00..=0x1f => {
            let lo = byte & 0x0f;
            let hex = if lo < 10 { b'0' + lo } else { b'a' + (lo - 10) };
            return ([b'\\', b'u', b'0', b'0', b'0' + (byte >> 4), hex], 6);
        }
        _ => return ([byte, 0, 0, 0, 0, 0], 1),
    };
    ([b'\\', short_escape, 0, 0, 0, 0], 2)
}

/// Return the escaped byte count, including the terminating NUL.
///
/// # Safety
///
/// The input must be valid for reads of `input_len` bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn ghc_rust_profiler_json_size(input: *const u8, input_len: usize) -> usize {
    let input = unsafe { slice::from_raw_parts(input, input_len) };
    1 + input.iter().map(|&byte| escape_byte(byte).1).sum::<usize>()
}

/// Escape the input bytes and write a terminating NUL. Return the count written.
///
/// # Safety
///
/// The input must be valid for reads of `input_len` bytes. The output must be
/// valid for writes of `output_len` bytes and must not overlap the input.
/// The output length must be the result of sizing the same input.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn ghc_rust_profiler_json_escape(
    input: *const u8,
    input_len: usize,
    output: *mut MaybeUninit<u8>,
    output_len: usize,
) -> usize {
    let input = unsafe { slice::from_raw_parts(input, input_len) };
    let output = unsafe { slice::from_raw_parts_mut(output, output_len) };
    let encoded = input
        .iter()
        .flat_map(|&byte| {
            let (bytes, len) = escape_byte(byte);
            bytes.into_iter().take(len)
        })
        .chain(core::iter::once(0));

    let mut written = 0;
    for (slot, byte) in output.iter_mut().zip(encoded) {
        slot.write(byte);
        written += 1;
    }
    written
}
