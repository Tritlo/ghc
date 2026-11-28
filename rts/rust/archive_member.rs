use core::ffi::c_int;
use core::slice;

#[repr(i32)]
enum ObjectFileFormat {
    // Keep these tags in sync with enum ObjectFileFormat in LoadArchive.c.
    NotObject = 0,
    CoffAmd64 = 1,
    CoffI386 = 2,
    CoffAArch64 = 3,
    Elf = 4,
    MachO32 = 5,
    MachO64 = 6,
}

/// Classify an archive member from its first nine bytes.
///
/// # Safety
///
/// When size exceeds two, buf must point to at least min(size, 9) readable
/// bytes in the same allocation. The caller must not modify those bytes
/// during the call.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_identify_object_file(
    buf: *const u8,
    size: usize,
) -> c_int {
    if size <= 2 {
        return ObjectFileFormat::NotObject as c_int;
    }
    let prefix = unsafe { slice::from_raw_parts(buf, size.min(9)) };
    classify(prefix) as c_int
}

fn classify(prefix: &[u8]) -> ObjectFileFormat {
    use ObjectFileFormat::*;

    // The C detector requires one byte past each candidate magic value.
    if let &[a, b, _, ..] = prefix {
        match u16::from_ne_bytes([a, b]) {
            0x8664 => return CoffAmd64,
            0x014c => return CoffI386,
            0xaa64 => return CoffAArch64,
            _ => {}
        }
    }

    if let &[a, b, c, d, _, ..] = prefix {
        let magic = [a, b, c, d];
        if magic == *b"\x7fELF" {
            return Elf;
        }
        match u32::from_ne_bytes(magic) {
            0xfeedface => return MachO32,
            0xfeedfacf => return MachO64,
            _ => {}
        }
    }

    if let &[a, b, c, d, e, f, g, h, _] = prefix {
        if u64::from_ne_bytes([a, b, c, d, e, f, g, h]) == 0x86640002ffff0000 {
            return CoffAmd64;
        }
    }

    NotObject
}
