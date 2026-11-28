use core::{
    ffi::{c_char, c_int, c_void},
    ptr, slice,
    sync::atomic::{AtomicI32, AtomicPtr, Ordering::Relaxed},
};

unsafe extern "C" {
    fn __rts_fopen(filename: *const c_char, mode: *const c_char) -> *mut c_void;
    fn ghc_rust_eventlog_open_failed(filename: *const c_char) -> !;
    fn ghc_rust_eventlog_init_mutex();
    fn ghc_rust_eventlog_acquire();
    fn ghc_rust_eventlog_release();
    fn ghc_rust_eventlog_close_mutex();

    fn getpid() -> c_int;
    fn strlen(value: *const c_char) -> usize;
    fn strdup(value: *const c_char) -> *mut c_char;
    fn stgMallocBytes(size: usize, label: *const c_char) -> *mut c_void;
    fn stgFree(ptr: *mut c_void);

    fn fwrite(data: *const u8, size: usize, count: usize, file: *mut c_void) -> usize;
    fn fflush(file: *mut c_void) -> c_int;
    fn fclose(file: *mut c_void) -> c_int;
}

// EventLog.c serializes init and stop with the writer callbacks. Rust owns the
// stream from open to close. C owns the mutex. libc serializes flushes with writes.
static EVENT_LOG_FILE: AtomicPtr<c_void> = AtomicPtr::new(ptr::null_mut());

// The child inherits this state from its parent. Reopening a default file in
// the same process also adds a PID. Explicit paths leave this state alone.
static EVENT_LOG_PID: AtomicI32 = AtomicI32::new(-1);

unsafe fn output_filename(program: *const c_char, output: *const c_char) -> *mut c_char {
    if !output.is_null() {
        return unsafe { strdup(output) };
    }

    unsafe {
        let len = strlen(program);
        let label = c"initEventLogFileWriter".as_ptr();
        let name = stgMallocBytes(len + 1, label).cast::<u8>();
        ptr::copy_nonoverlapping(program.cast::<u8>(), name, len + 1);
        // Linux getpid returns a positive pid_t (at most seven digits).
        // Keep the stock allocation size, with space for any c_int result.
        let mut digits = [0; 21];
        let mut first = digits.len();
        let mut pid = getpid() as u64;
        if EVENT_LOG_PID.swap(pid as c_int, Relaxed) != -1 {
            // A u64 needs at most twenty decimal digits. Leave one byte for
            // the separator when writing backward into the stack buffer.
            for digit in digits[1..].iter_mut().rev() {
                *digit = b'0' + (pid % 10) as u8;
                first -= 1;
                pid /= 10;
                if pid == 0 {
                    break;
                }
            }
            first -= 1;
            digits.as_mut_ptr().add(first).write(b'.');
        }
        let suffix = slice::from_raw_parts(digits.as_ptr().add(first), digits.len() - first);
        let extension = b".eventlog\0";
        let filename =
            stgMallocBytes(len + 20.max(suffix.len() + extension.len()), label).cast::<u8>();
        ptr::copy_nonoverlapping(name, filename, len);
        let end = filename.add(len);
        ptr::copy_nonoverlapping(suffix.as_ptr(), end, suffix.len());
        ptr::copy_nonoverlapping(extension.as_ptr(), end.add(suffix.len()), extension.len());
        stgFree(name.cast());
        filename.cast()
    }
}

/// Open the file and initialize the writer mutex.
/// # Safety
/// No other writer callback may run during initialization. The program name,
/// or the non-null output override, must be a valid C string.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_eventlog_init(
    program: *const c_char,
    output: *const c_char,
) {
    let filename = unsafe { output_filename(program, output) };
    let file = unsafe { __rts_fopen(filename, c"wb+".as_ptr()) };
    if file.is_null() {
        unsafe { ghc_rust_eventlog_open_failed(filename) };
    }
    unsafe {
        stgFree(filename.cast());
        ghc_rust_eventlog_init_mutex();
    }
    EVENT_LOG_FILE.store(file, Relaxed);
}

/// Write all bytes, or return false when a write reports no progress.
///
/// # Safety
///
/// The writer must be initialized. The buffer must be readable for
/// `remaining` bytes for the duration of the call.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_eventlog_write(
    mut data: *const u8,
    mut remaining: usize,
) -> bool {
    unsafe { ghc_rust_eventlog_acquire() };
    let file = EVENT_LOG_FILE.load(Relaxed);
    while remaining > 0 {
        let written = unsafe { fwrite(data, 1, remaining, file) };
        if written == 0 {
            unsafe { ghc_rust_eventlog_release() };
            return false;
        }
        remaining -= written;
        data = unsafe { data.add(written) };
    }
    unsafe { ghc_rust_eventlog_release() };

    unsafe { ghc_rust_eventlog_flush() };
    true
}

/// Flush the file if it is open.
///
/// # Safety
///
/// Initialization and shutdown must be serialized with this call.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_eventlog_flush() {
    let file = EVENT_LOG_FILE.load(Relaxed);
    if !file.is_null() {
        unsafe { fflush(file) };
    }
}

/// Close the file and destroy the writer mutex.
///
/// # Safety
///
/// The writer must be initialized. No other writer callback may run during
/// shutdown.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_eventlog_stop() {
    let file = EVENT_LOG_FILE.load(Relaxed);
    if !file.is_null() {
        unsafe { fclose(file) };
        EVENT_LOG_FILE.store(ptr::null_mut(), Relaxed);
    }
    unsafe { ghc_rust_eventlog_close_mutex() };
}
