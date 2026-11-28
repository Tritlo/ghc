use core::ffi::{c_int, c_void};
use core::mem::{offset_of, size_of};
use core::ptr::{copy_nonoverlapping, write_bytes};
use core::sync::atomic::{AtomicUsize, Ordering::Relaxed};

core::arch::global_asm!(
    ".hidden ghc_rust_closure_table_grow",
    ".hidden ghc_rust_closure_table_init",
    ".hidden ghc_rust_closure_table_mark",
    ".hidden ghc_rust_closure_table_insert",
    ".hidden ghc_rust_closure_table_insert_debug",
);

// See Note [Closure table Rust layout] in rts/ClosureTable.c.
#[repr(C)]
pub(super) struct ClosureTable {
    arr: *mut c_void,
    free: *mut c_void,
    free_hd: c_int,
    elems: c_int,
    capacity: c_int,
    compact: c_int,
}

unsafe extern "C" {
    static stg_MUT_ARR_PTRS_DIRTY_info: u8;
}

const _: () = {
    assert!(offset_of!(ClosureTable, arr) == 0);
    assert!(offset_of!(ClosureTable, free) == size_of::<*mut c_void>());
    assert!(offset_of!(ClosureTable, free_hd) == 2 * size_of::<*mut c_void>());
    assert!(offset_of!(ClosureTable, elems) == 2 * size_of::<*mut c_void>() + size_of::<c_int>());
    assert!(
        offset_of!(ClosureTable, capacity) == 2 * size_of::<*mut c_void>() + 2 * size_of::<c_int>()
    );
    assert!(
        offset_of!(ClosureTable, compact) == 2 * size_of::<*mut c_void>() + 3 * size_of::<c_int>()
    );
    assert!(size_of::<ClosureTable>() == 2 * size_of::<*mut c_void>() + 4 * size_of::<c_int>());
};

unsafe extern "C" {
    fn allocateMutArrPtrs(
        cap: *mut c_void,
        count: usize,
        init: *mut c_void,
        ccs: *mut c_void,
    ) -> *mut c_void;
    fn allocateArrBytes(cap: *mut c_void, bytes: usize, ccs: *mut c_void) -> *mut c_void;
    fn mutArrPtrsCardTableSize(count: usize) -> usize;
    fn recordClosureMutated(cap: *mut c_void, array: *mut c_void);
    static mut nonmoving_write_barrier_enabled: usize;
    fn updateRemembSetPushClosure(cap: *mut c_void, closure: *mut c_void);
}

/// Grow both heap arrays. Publish them only after initialization and GC registration.
///
/// # Safety
///
/// The caller owns the table and its capability. The offsets are the payload
/// offsets of StgMutArrPtrs and StgArrBytes for this RTS way.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_closure_table_grow(
    table: *mut ClosureTable,
    cap: *mut c_void,
    capacity: c_int,
    ccs: *mut c_void,
    slots_offset: usize,
    links_offset: usize,
) -> bool {
    unsafe {
        let old_capacity = (*table).capacity;
        if capacity <= old_capacity {
            return false;
        }
        let new_count = capacity as usize;
        if new_count > (usize::MAX - (size_of::<usize>() - 1)) / size_of::<c_int>() {
            return false;
        }
        let array = allocateMutArrPtrs(cap, new_count, core::ptr::null_mut(), ccs);
        if array.is_null() {
            return false;
        }
        let links_array = allocateArrBytes(cap, new_count * size_of::<c_int>(), ccs);
        if links_array.is_null() {
            return false;
        }
        let slots = array.byte_add(slots_offset).cast::<*mut c_void>();
        let links = links_array.byte_add(links_offset);
        let old_count = old_capacity as usize;
        let old_cards = mutArrPtrsCardTableSize(old_count);
        let new_cards = mutArrPtrsCardTableSize(new_count);
        if old_count != 0 {
            // An empty table points to static sentinels without array payloads.
            let old_slots = (*table).arr.byte_add(slots_offset).cast::<*mut c_void>();
            let old_links = (*table).free.byte_add(links_offset).cast::<usize>();
            copy_nonoverlapping(old_slots, slots, old_count);
            copy_nonoverlapping(old_slots.add(old_count), slots.add(new_count), old_cards);
            // Copy complete words, including the padding of an odd-sized free list.
            let link_words = (old_count * size_of::<c_int>()).div_ceil(size_of::<usize>());
            copy_nonoverlapping(old_links, links.cast::<usize>(), link_words);
        }
        let sentinel = (&raw const stg_CLOSURE_TABLE_NULL_closure)
            .cast_mut()
            .cast();
        for index in old_count..new_count {
            slots.add(index).write(sentinel);
        }
        write_bytes(slots.add(new_count + old_cards), 0, new_cards - old_cards);
        let next = links.cast::<c_int>();
        for index in old_count..new_count - 1 {
            next.add(index).write((index + 1) as c_int);
        }
        next.add(new_count - 1).write((*table).free_hd);
        recordClosureMutated(cap, array);
        (*table).arr = array;
        (*table).free_hd = old_capacity;
        (*table).free = links_array;
        (*table).capacity = capacity;
        true
    }
}

/// Initialize one table with the C-owned null closure sentinel.
///
/// # Safety
///
/// `table` is a valid, exclusively owned ClosureTable. C checks its layout.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_closure_table_init(
    table: *mut ClosureTable,
    mode: c_int,
    sentinel: *mut c_void,
) {
    unsafe {
        (&raw mut (*table).arr).write(sentinel);
        (&raw mut (*table).free).write(sentinel);
        (&raw mut (*table).free_hd).write(-1);
        (&raw mut (*table).elems).write(0);
        (&raw mut (*table).capacity).write(0);
        (&raw mut (*table).compact).write(mode);
    }
}

/// Visit both live root slots in the same order as C.
///
/// # Safety
///
/// `table` remains valid during both callbacks. The collector may replace
/// either root pointer through its slot. C checks the table layout.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_closure_table_mark(
    table: *mut ClosureTable,
    evac: unsafe extern "C" fn(*mut c_void, *mut *mut c_void),
    user: *mut c_void,
) {
    unsafe {
        evac(user, &raw mut (*table).arr);
        evac(user, &raw mut (*table).free);
    }
}

/// Insert one closure into a free slot and update its GC metadata.
///
/// # Safety
///
/// C owns the table and checks that its free head names an empty slot. C
/// supplies the live payload, card, and info slots using RTS array geometry.
/// `next_free` is the current free-list link. C checks the table layout and
/// marks the used free-list entry in DEBUG builds.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_closure_table_insert(
    table: *mut ClosureTable,
    value: *mut c_void,
    slot: *mut *mut c_void,
    card: *mut u8,
    info_slot: *mut *const c_void,
    next_free: c_int,
) -> c_int {
    let ix = unsafe { (&raw const (*table).free_hd).read() };
    unsafe {
        slot.write(value);
        card.write(1);
        info_slot.write((&raw const stg_MUT_ARR_PTRS_DIRTY_info).cast());
        (&raw mut (*table).free_hd).write(next_free);
        let elems = &raw mut (*table).elems;
        elems.write(elems.read() + 1);
    }
    ix
}

unsafe extern "C" {
    static stg_CLOSURE_TABLE_NULL_closure: u8;
}

core::arch::global_asm!(
    ".hidden ghc_rust_closure_table_remove_sparse",
    ".hidden ghc_rust_closure_table_remove_compact",
    ".hidden ghc_rust_closure_table_remove_sparse_native",
    ".hidden ghc_rust_closure_table_remove_compact_native",
);

const NATIVE_SLOTS_OFFSET: usize = 3 * size_of::<usize>();

/// Link the released index at the head of the free list.
unsafe fn recycle(table: *mut ClosureTable, free_link: *mut c_int, ix: c_int) {
    unsafe {
        free_link.write((*table).free_hd);
        (*table).free_hd = ix;
        (*table).elems -= 1;
    }
}

// See Note [Closure table removal barrier in Rust] in rts/ClosureTable.c.
unsafe fn barrier_enabled(cap: *mut c_void) -> bool {
    !cap.is_null()
        && unsafe {
            AtomicUsize::from_ptr(&raw mut nonmoving_write_barrier_enabled).load(Relaxed) != 0
        }
}

#[inline(always)]
unsafe fn remove_sparse_body(
    table: *mut ClosureTable,
    cap: *mut c_void,
    ix: c_int,
    slots_offset: usize,
    barrier_active: bool,
) {
    unsafe {
        let slot = (*table)
            .arr
            .byte_add(slots_offset)
            .cast::<*mut c_void>()
            .add(ix as usize);
        let free_link = (*table)
            .free
            .byte_add(slots_offset - size_of::<usize>())
            .cast::<c_int>()
            .add(ix as usize);
        if barrier_active {
            updateRemembSetPushClosure(cap, slot.read());
        }
        slot.write(
            (&raw const stg_CLOSURE_TABLE_NULL_closure)
                .cast_mut()
                .cast(),
        );
        recycle(table, free_link, ix);
    }
}

/// Clear an occupied slot. Run the nonmoving write barrier first when enabled.
///
/// # Safety
///
/// The caller owns the table. `slots_offset` is the checked payload offset for
/// this RTS way. A null `barrier_cap` disables the barrier in the vanilla RTS.
#[unsafe(no_mangle)]
unsafe extern "C" fn ghc_rust_closure_table_remove_sparse(
    table: *mut ClosureTable,
    barrier_cap: *mut c_void,
    ix: c_int,
    slots_offset: usize,
) {
    unsafe {
        remove_sparse_body(
            table,
            barrier_cap,
            ix,
            slots_offset,
            barrier_enabled(barrier_cap),
        );
    }
}

/// Remove with the native array layout. C checks both payload offsets.
#[unsafe(no_mangle)]
unsafe extern "C" fn ghc_rust_closure_table_remove_sparse_native(
    table: *mut ClosureTable,
    barrier_cap: *mut c_void,
    ix: c_int,
) {
    unsafe {
        if barrier_enabled(barrier_cap) {
            remove_sparse_native_barrier(table, barrier_cap, ix);
        } else {
            remove_sparse_body(table, barrier_cap, ix, NATIVE_SLOTS_OFFSET, false);
        }
    }
}

#[cold]
#[inline(never)]
unsafe fn remove_sparse_native_barrier(table: *mut ClosureTable, cap: *mut c_void, ix: c_int) {
    unsafe {
        remove_sparse_body(table, cap, ix, NATIVE_SLOTS_OFFSET, true);
    }
}

#[inline(always)]
unsafe fn remove_compact_body(
    table: *mut ClosureTable,
    cap: *mut c_void,
    gap: c_int,
    last: c_int,
    slots_offset: usize,
    barrier_active: bool,
) {
    unsafe {
        let payload = (*table).arr.byte_add(slots_offset).cast::<*mut c_void>();
        let gap_slot = payload.add(gap as usize);
        let last_slot = payload.add(last as usize);
        if barrier_active {
            updateRemembSetPushClosure(cap, gap_slot.read());
        }
        gap_slot.write(last_slot.read());
        last_slot.write(
            (&raw const stg_CLOSURE_TABLE_NULL_closure)
                .cast_mut()
                .cast(),
        );
        payload
            .add((*table).capacity as usize)
            .cast::<u8>()
            .add((gap as usize) >> 7)
            .write(1);
        let free_link = (*table)
            .free
            .byte_add(slots_offset - size_of::<usize>())
            .cast::<c_int>()
            .add(last as usize);
        recycle(table, free_link, last);
    }
}

/// Move the last entry into the gap. Mark the destination card even when
/// the caller removes the last entry itself.
///
/// # Safety
///
/// The caller owns the table. `slots_offset` is the checked payload offset for
/// this RTS way. The gap and last slots are occupied. The card belongs to the
/// gap. A null `barrier_cap` disables the barrier in the vanilla RTS.
#[unsafe(no_mangle)]
unsafe extern "C" fn ghc_rust_closure_table_remove_compact(
    table: *mut ClosureTable,
    barrier_cap: *mut c_void,
    gap: c_int,
    ix_from: *mut c_int,
    ix_to: *mut c_int,
    slots_offset: usize,
) {
    unsafe {
        let last = (*table).elems - 1;
        ix_from.write(last);
        ix_to.write(gap);
        remove_compact_body(
            table,
            barrier_cap,
            gap,
            last,
            slots_offset,
            barrier_enabled(barrier_cap),
        );
    }
}

/// Remove from a compact table with the native array layout.
/// C checks both payload offsets.
#[unsafe(no_mangle)]
unsafe extern "C" fn ghc_rust_closure_table_remove_compact_native(
    table: *mut ClosureTable,
    barrier_cap: *mut c_void,
    gap: c_int,
    ix_from: *mut c_int,
    ix_to: *mut c_int,
) {
    unsafe {
        let last = (*table).elems - 1;
        ix_from.write(last);
        ix_to.write(gap);
        if barrier_enabled(barrier_cap) {
            remove_compact_native_barrier(table, barrier_cap, gap, last);
        } else {
            remove_compact_body(table, barrier_cap, gap, last, NATIVE_SLOTS_OFFSET, false);
        }
    }
}

#[cold]
#[inline(never)]
unsafe fn remove_compact_native_barrier(
    table: *mut ClosureTable,
    cap: *mut c_void,
    gap: c_int,
    last: c_int,
) {
    unsafe {
        remove_compact_body(table, cap, gap, last, NATIVE_SLOTS_OFFSET, true);
    }
}

/// Insert one closure and mark its free-list entry as used in DEBUG builds.
///
/// # Safety
///
/// The insertion contract applies. `free_link` is the entry at the current
/// free head. C checks that the entry is free before this call.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_closure_table_insert_debug(
    table: *mut ClosureTable,
    value: *mut c_void,
    slot: *mut *mut c_void,
    card: *mut u8,
    info_slot: *mut *const c_void,
    free_link: *mut c_int,
) -> c_int {
    let next_free = unsafe { free_link.read() };
    let ix =
        unsafe { ghc_rust_closure_table_insert(table, value, slot, card, info_slot, next_free) };
    unsafe { free_link.write(-2) };
    ix
}
