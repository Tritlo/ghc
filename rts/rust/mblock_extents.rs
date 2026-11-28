use core::{
    ffi::{c_char, c_void},
    mem,
    ptr::{self, NonNull},
};

unsafe extern "C" {
    fn stgMallocBytes(size: usize, name: *const c_char) -> *mut c_void;
    fn stgFree(ptr: *mut c_void);
}

type Link = Option<NonNull<Extent>>;

struct Extent {
    start: usize,
    end: usize,
    next: Link,
}

impl Extent {
    /// Allocate a node with the RTS allocator.
    fn new(start: usize, end: usize, next: Link) -> NonNull<Self> {
        unsafe {
            // A nonzero stgMallocBytes allocation returns aligned storage or exits.
            let node = stgMallocBytes(mem::size_of::<Self>(), c"freeMBlocks".as_ptr()).cast();
            ptr::write(node, Self { start, end, next });
            NonNull::new_unchecked(node)
        }
    }
}

struct Index {
    head: Link,
    watermark: usize,
}

// The RTS storage manager serializes mutations and keeps the index stable
// during iteration. Each link owns its node. C receives an opaque cursor
// valid only until the next mutation. Free extents do not touch or overlap,
// and their ends are strictly below the high-water mark.
static mut INDEX: Index = Index {
    head: None,
    watermark: 0,
};

impl Index {
    /// Free all extent metadata and set the next fresh address.
    fn reset(&mut self, watermark: usize) {
        while let Some(node) = self.head {
            unsafe {
                self.head = node.as_ref().next;
                stgFree(node.as_ptr().cast());
            }
        }
        self.watermark = watermark;
    }

    /// Take the low end of the first extent that has enough space.
    fn take_reusable(&mut self, size: usize) -> Option<usize> {
        let mut link = &mut self.head;
        while let Some(mut node) = *link {
            let extent = unsafe { node.as_mut() };
            if extent.end - extent.start < size {
                link = &mut extent.next;
                continue;
            }

            let address = extent.start;
            extent.start += size;
            if extent.start == extent.end {
                *link = extent.next;
                unsafe { stgFree(node.as_ptr().cast()) };
            }
            return Some(address);
        }
        None
    }

    /// Insert a freed extent and merge adjacent extents. Shrink the watermark
    /// when the result reaches the end of the committed range.
    fn release(&mut self, start: usize, size: usize) -> bool {
        let Some(end) = start.checked_add(size) else {
            return false;
        };
        if size == 0 || end > self.watermark {
            return false;
        }

        let mut link = &mut self.head;
        while let Some(mut node) = *link {
            let extent = unsafe { node.as_mut() };
            if extent.end < start {
                link = &mut extent.next;
                continue;
            }

            if extent.end == start {
                if end == self.watermark && extent.next.is_none() {
                    self.watermark = extent.start;
                    *link = extent.next;
                    unsafe { stgFree(node.as_ptr().cast()) };
                    return true;
                }

                if let Some(next) = extent.next {
                    let following = unsafe { next.as_ref() };
                    if end > following.start {
                        return false;
                    }
                    if end == following.start {
                        extent.end = following.end;
                        extent.next = following.next;
                        unsafe { stgFree(next.as_ptr().cast()) };
                        return true;
                    }
                }
                extent.end = end;
                return true;
            }

            if end > extent.start {
                return false;
            }
            if end == extent.start {
                extent.start = start;
            } else {
                *link = Some(Extent::new(start, end, *link));
            }
            return true;
        }

        if end == self.watermark {
            self.watermark = start;
        } else {
            *link = Some(Extent::new(start, end, None));
        }
        true
    }

    /// Find the first committed megablock at a valid iteration position.
    fn find(&self, mut next: Link, mut address: usize) -> (usize, Link) {
        while let Some(node) = next {
            let extent = unsafe { node.as_ref() };
            if address < extent.start {
                break;
            }
            if address == extent.start {
                address = extent.end;
            }
            next = extent.next;
        }
        let address = if address < self.watermark { address } else { 0 };
        (address, next)
    }
}

/// Reset the index before allocator use or at shutdown.
///
/// # Safety
///
/// The storage manager must exclude every other access.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn rts_rust_mblock_reset(watermark: usize) {
    unsafe { &mut *(&raw mut INDEX) }.reset(watermark);
}

/// Select a reusable extent or identify a fresh range within the limit.
/// A zero return indicates that the reservation cannot satisfy the request.
///
/// # Safety
///
/// The storage manager must serialize access. The output flag must be valid
/// for writes. The size must be a nonzero whole number of megablocks.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn rts_rust_mblock_take(
    size: usize,
    limit: usize,
    fresh: *mut bool,
) -> usize {
    let index = unsafe { &mut *(&raw mut INDEX) };
    if let Some(address) = index.take_reusable(size) {
        unsafe { fresh.write(false) };
        return address;
    }
    if let Some(end) = index.watermark.checked_add(size)
        && end <= limit
    {
        unsafe { fresh.write(true) };
        return index.watermark;
    }
    unsafe { fresh.write(false) };
    0
}

/// Advance the high-water mark after a successful fresh OS commit.
///
/// # Safety
///
/// The storage manager must hold the same exclusion as for selection. The
/// size must match a fresh extent selected immediately before the commit.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn rts_rust_mblock_commit_fresh(size: usize) {
    unsafe { (*(&raw mut INDEX)).watermark += size };
}

/// Record a decommitted range. Return false for an invalid range.
///
/// # Safety
///
/// The storage manager must exclude other accesses. The range must belong
/// to the heap reservation and start and end at megablock boundaries.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn rts_rust_mblock_release(address: usize, size: usize) -> bool {
    unsafe { &mut *(&raw mut INDEX) }.release(address, size)
}

/// Continue an ascending traversal and optionally preserve its cursor.
///
/// # Safety
///
/// The storage manager must keep the index stable during traversal. A
/// nonnull state must point to an opaque cursor from the same traversal
/// unless this is its first call. The address must be megablock-aligned.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn rts_rust_mblock_find(
    state: *mut *mut c_void,
    address: usize,
    first: bool,
) -> usize {
    let index = unsafe { &*(&raw const INDEX) };
    let next = if first || state.is_null() {
        index.head
    } else {
        NonNull::new(unsafe { state.read() }.cast())
    };
    let (address, next) = index.find(next, address);
    if !state.is_null() {
        let cursor = next.map_or(ptr::null_mut(), |node| node.as_ptr().cast());
        unsafe { state.write(cursor) };
    }
    address
}

/// Read the high-water mark for diagnostics.
///
/// # Safety
///
/// The storage manager must exclude concurrent mutations.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn rts_rust_mblock_watermark() -> usize {
    unsafe { (*(&raw const INDEX)).watermark }
}
