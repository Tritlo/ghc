use core::ffi::c_void;
use core::mem::{align_of, size_of};
use core::ptr::{null_mut, write_bytes};
use core::sync::atomic::{AtomicPtr, AtomicUsize, Ordering};

core::arch::global_asm!(
    ".hidden ghc_rust_schedule_finalizers",
    ".hidden ghc_rust_pending_finalizers",
    ".hidden ghc_rust_run_some_finalizers",
);

const _: () = {
    assert!(size_of::<AtomicPtr<u8>>() == size_of::<*mut u8>());
    assert!(align_of::<AtomicPtr<u8>>() == align_of::<*mut u8>());
    assert!(size_of::<AtomicUsize>() == size_of::<usize>());
    assert!(align_of::<AtomicUsize>() == align_of::<usize>());
};

static FINALIZER_LIST: AtomicPtr<u8> = AtomicPtr::new(null_mut());
static PENDING_FINALIZERS: AtomicUsize = AtomicUsize::new(0);
static FINALIZER_LOCK: AtomicUsize = AtomicUsize::new(0);

unsafe extern "C" {
    fn allocateMutArrPtrs(
        cap: *mut c_void,
        count: usize,
        init: *mut c_void,
        ccs: *mut c_void,
    ) -> *mut c_void;
    fn mutArrPtrsCardTableSize(count: usize) -> usize;
    fn rts_mkInt(cap: *mut c_void, value: isize) -> *mut c_void;
    fn rts_apply(cap: *mut c_void, function: *mut c_void, argument: *mut c_void) -> *mut c_void;
    fn createIOThread(cap: *mut c_void, stack_size: usize, action: *mut c_void) -> *mut c_void;
    fn scheduleThread(cap: *mut c_void, thread: *mut c_void);
    fn exitHeapOverflow() -> !;
    static stg_MUT_ARR_PTRS_FROZEN_CLEAN_info: u8;
    static stg_DEAD_WEAK_info: u8;
    static stg_NO_FINALIZER_closure: u8;
}

/// Append dead weak pointers, mark the new entries, and publish their count.
/// The GC owns `list`. Earlier entries can still await the idle drain.
/// C supplies the weak link offset and any assertion or profiling header action.
unsafe fn prepare_finalizers(
    list: *mut u8,
    link_offset: usize,
    prepare_header: Option<unsafe extern "C" fn(*mut u8)>,
) -> usize {
    unsafe {
        let mut tail = FINALIZER_LIST.as_ptr();
        loop {
            let weak = AtomicPtr::from_ptr(tail).load(Ordering::Relaxed);
            if weak.is_null() {
                break;
            }
            tail = weak.byte_add(link_offset).cast::<*mut u8>();
        }
        AtomicPtr::from_ptr(tail).store(list, Ordering::SeqCst);

        let mut actions = 0;
        let mut entries = 0;
        let mut weak = list;
        while !weak.is_null() {
            if let Some(prepare_header) = prepare_header {
                prepare_header(weak);
            }
            let finalizer = weak
                .byte_add(link_offset - size_of::<usize>())
                .cast::<*mut u8>()
                .read();
            if finalizer.cast_const() != &raw const stg_NO_FINALIZER_closure {
                actions += 1;
            }
            entries += 1;
            AtomicPtr::from_ptr(weak.cast::<*mut u8>()).store(
                (&raw const stg_DEAD_WEAK_info).cast_mut(),
                Ordering::Relaxed,
            );
            weak = weak.byte_add(link_offset).cast::<*mut u8>().read();
        }
        PENDING_FINALIZERS.fetch_add(entries, Ordering::SeqCst);
        actions
    }
}

/// Prepare dead weak pointers and schedule one Haskell batch when needed.
/// C supplies the RTS way's header action, trace, CCS, and array offset.
#[unsafe(no_mangle)]
unsafe extern "C" fn ghc_rust_schedule_finalizers(
    cap: *mut c_void,
    list: *mut u8,
    stack_size: u32,
    ccs: *mut c_void,
    link_offset: usize,
    payload_offset: usize,
    runner: unsafe extern "C" fn() -> *mut c_void,
    prepare_header: Option<unsafe extern "C" fn(*mut u8)>,
    trace_batch: Option<unsafe extern "C" fn(usize)>,
) {
    unsafe {
        let count = prepare_finalizers(list, link_offset, prepare_header);
        if count == 0 {
            return;
        }
        if let Some(trace_batch) = trace_batch {
            trace_batch(count);
        }
        let array = make_finalizer_batch(cap, list, count, ccs, link_offset, payload_offset);
        if array.is_null() {
            exitHeapOverflow();
        }
        let action = rts_apply(cap, runner(), rts_mkInt(cap, count as isize));
        let action = rts_apply(cap, action, array);
        let thread = createIOThread(cap, stack_size as usize, action);
        scheduleThread(cap, thread);
    }
}

/// Read the pending count for the GC assertion and native trace.
#[unsafe(no_mangle)]
unsafe extern "C" fn ghc_rust_pending_finalizers() -> usize {
    PENDING_FINALIZERS.load(Ordering::SeqCst)
}

/// Claim the drain lock, run callbacks, and release the lock.
/// C supplies a task flag and optional trace hooks after a successful claim.
#[unsafe(no_mangle)]
unsafe extern "C" fn ghc_rust_run_some_finalizers(
    all: bool,
    callbacks_offset: usize,
    link_offset: usize,
    payload_offset: usize,
    running_flag: unsafe extern "C" fn() -> *mut bool,
    trace_begin: Option<unsafe extern "C" fn(usize)>,
    trace_end: Option<unsafe extern "C" fn(usize)>,
) -> bool {
    if PENDING_FINALIZERS.load(Ordering::Relaxed) == 0 {
        return false;
    }
    if FINALIZER_LOCK
        .compare_exchange(0, 1, Ordering::SeqCst, Ordering::SeqCst)
        .is_err()
    {
        return false;
    }
    unsafe {
        if let Some(trace_begin) = trace_begin {
            trace_begin(PENDING_FINALIZERS.load(Ordering::Relaxed));
        }
        let running = running_flag();
        if !running.is_null() {
            running.write(true);
        }
        let mut cursor = FINALIZER_LIST.load(Ordering::Relaxed);
        // Bound each idle step so the capability can respond to new work.
        let limit = if all { usize::MAX } else { 100 };
        let count = super::c_finalizers::drain_c_finalizers(
            &mut cursor,
            limit,
            callbacks_offset,
            link_offset,
            payload_offset,
        );
        FINALIZER_LIST.store(cursor, Ordering::Relaxed);
        PENDING_FINALIZERS.fetch_sub(count, Ordering::SeqCst);
        if !running.is_null() {
            running.write(false);
        }
        if let Some(trace_end) = trace_end {
            trace_end(count);
        }
    }
    let more = PENDING_FINALIZERS.load(Ordering::Relaxed) != 0;
    FINALIZER_LOCK.store(0, Ordering::Release);
    more
}

// The producer has counted the Haskell finalizers in this GC-owned list.
// runFinalizerBatch reads the completed array from the last slot to the first.
unsafe fn make_finalizer_batch(
    cap: *mut c_void,
    mut weak: *mut u8,
    count: usize,
    ccs: *mut c_void,
    link_offset: usize,
    payload_offset: usize,
) -> *mut c_void {
    unsafe {
        let array = allocateMutArrPtrs(cap, count, null_mut(), ccs);
        if array.is_null() {
            return array;
        }
        array
            .cast::<*const u8>()
            .write(&raw const stg_MUT_ARR_PTRS_FROZEN_CLEAN_info);
        let mut slot = array.byte_add(payload_offset).cast::<*mut u8>();
        while !weak.is_null() {
            let finalizer = weak
                .add(link_offset - size_of::<usize>())
                .cast::<*mut u8>()
                .read();
            if finalizer.cast_const() != &raw const stg_NO_FINALIZER_closure {
                slot.write(finalizer);
                slot = slot.add(1);
            }
            weak = weak.add(link_offset).cast::<*mut u8>().read();
        }
        write_bytes(slot.cast::<usize>(), 0xff, mutArrPtrsCardTableSize(count));
        array
    }
}
