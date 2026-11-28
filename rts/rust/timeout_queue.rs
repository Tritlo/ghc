use core::ffi::{c_int, c_void};
use core::mem::{offset_of, size_of};

core::arch::global_asm!(
    ".hidden ghc_rust_timeout_queue_insert",
    ".hidden ghc_rust_timeout_queue_insert_release",
    ".hidden ghc_rust_timeout_queue_delete_min",
    ".hidden ghc_rust_timeout_queue_delete",
);

const RELEASE_PARENT_OFFSET: usize = 16;

// See Note [Timeout queue field offsets] in rts/TimeoutQueue.c.
#[repr(C)]
struct HeapSuffix {
    parent: *mut c_void,
    a: *mut c_void,
    b: *mut c_void,
    rank: u32,
    waketime: i64,
}

const _: () = {
    assert!(size_of::<HeapSuffix>() == 40);
    assert!(offset_of!(HeapSuffix, parent) == 0);
    assert!(offset_of!(HeapSuffix, a) == 8);
    assert!(offset_of!(HeapSuffix, b) == 16);
    assert!(offset_of!(HeapSuffix, rank) == 24);
    assert!(offset_of!(HeapSuffix, waketime) == 32);
};

unsafe fn suffix(node: *mut c_void, parent_offset: usize) -> *mut HeapSuffix {
    unsafe { node.cast::<u8>().add(parent_offset).cast::<HeapSuffix>() }
}

unsafe fn rank(node: *mut c_void, empty: *mut c_void, parent_offset: usize) -> u32 {
    if node == empty {
        0
    } else {
        unsafe { (&raw const (*suffix(node, parent_offset)).rank).read() }
    }
}

/// Insert one initialized timeout into a leftist heap.
///
/// # Safety
///
/// C owns the queue, all nodes, and the non-null empty sentinel. It gives this
/// call exclusive access to the queue. The new node has rank one and empty
/// children. `parent_offset` and the relative field offsets match the checked
/// C layout. The optional counter pointers are valid for this call.
#[inline(always)]
unsafe fn insert(
    root: *mut *mut c_void,
    new_node: *mut c_void,
    empty: *mut c_void,
    parent_offset: usize,
    insert_down_count: *mut c_int,
    leftify_count: *mut c_int,
) {
    let mut parent = empty;
    let mut parent_child = root;
    let mut node = unsafe { root.read() };
    let new_fields = unsafe { suffix(new_node, parent_offset) };
    let deadline = unsafe { (&raw const (*new_fields).waketime).read() };
    let mut down_steps = 0;

    loop {
        if node == empty {
            break;
        }
        let fields = unsafe { suffix(node, parent_offset) };
        let node_deadline = unsafe { (&raw const (*fields).waketime).read() };
        if deadline <= node_deadline {
            unsafe {
                (&raw mut (*new_fields).a).write(node);
                (&raw mut (*fields).parent).write(new_node);
            }
            break;
        }
        parent = node;
        parent_child = unsafe { &raw mut (*fields).b };
        node = unsafe { parent_child.read() };
        down_steps += 1;
    }

    unsafe {
        (&raw mut (*new_fields).parent).write(parent);
        parent_child.write(new_node);
    }

    let mut up_steps = 0;
    unsafe { leftify::<true>(parent, empty, empty, parent_offset, &mut up_steps) };

    if !insert_down_count.is_null() {
        unsafe { *insert_down_count += down_steps };
    }
    if !leftify_count.is_null() {
        unsafe { *leftify_count += up_steps };
    }
}

/// Insert with the offset and counters selected for the RTS way.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_timeout_queue_insert(
    root: *mut *mut c_void,
    new_node: *mut c_void,
    empty: *mut c_void,
    parent_offset: usize,
    insert_down_count: *mut c_int,
    leftify_count: *mut c_int,
) {
    unsafe {
        insert(
            root,
            new_node,
            empty,
            parent_offset,
            insert_down_count,
            leftify_count,
        )
    }
}

/// Insert with the checked nonprofiling release layout.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_timeout_queue_insert_release(
    root: *mut *mut c_void,
    new_node: *mut c_void,
    empty: *mut c_void,
) {
    unsafe {
        insert(
            root,
            new_node,
            empty,
            RELEASE_PARENT_OFFSET,
            core::ptr::null_mut(),
            core::ptr::null_mut(),
        )
    }
}

// Link the merged subtree to its parent. Return the lowest node that needs
// its rank checked. The two input heaps use the non-null empty sentinel.
unsafe fn merge_down(
    mut first: *mut c_void,
    mut second: *mut c_void,
    mut parent: *mut c_void,
    mut parent_child: *mut *mut c_void,
    empty: *mut c_void,
    parent_offset: usize,
    steps: &mut c_int,
) -> *mut c_void {
    loop {
        let node = if second == empty {
            if first == empty {
                unsafe { parent_child.write(empty) };
                return parent;
            }
            first
        } else if first == empty {
            second
        } else {
            let first_fields = unsafe { suffix(first, parent_offset) };
            let second_fields = unsafe { suffix(second, parent_offset) };
            let first_time = unsafe { (&raw const (*first_fields).waketime).read() };
            let second_time = unsafe { (&raw const (*second_fields).waketime).read() };
            let selected = if first_time <= second_time {
                let selected = first;
                first = unsafe { (&raw const (*first_fields).b).read() };
                selected
            } else {
                let selected = second;
                second = unsafe { (&raw const (*second_fields).b).read() };
                selected
            };
            let selected_fields = unsafe { suffix(selected, parent_offset) };
            unsafe {
                (&raw mut (*selected_fields).parent).write(parent);
                parent_child.write(selected);
            }
            parent = selected;
            parent_child = unsafe { &raw mut (*selected_fields).b };
            *steps += 1;
            continue;
        };
        let fields = unsafe { suffix(node, parent_offset) };
        unsafe {
            (&raw mut (*fields).parent).write(parent);
            parent_child.write(node);
        }
        return node;
    }
}

#[inline(always)]
unsafe fn leftify<const STOP_ON_UNCHANGED: bool>(
    mut node: *mut c_void,
    target: *mut c_void,
    empty: *mut c_void,
    parent_offset: usize,
    steps: &mut c_int,
) {
    while node != target {
        let fields = unsafe { suffix(node, parent_offset) };
        let left = unsafe { (&raw const (*fields).a).read() };
        let right = unsafe { (&raw const (*fields).b).read() };
        let left_rank = unsafe { rank(left, empty, parent_offset) };
        let right_rank = unsafe { rank(right, empty, parent_offset) };
        let rank_slot = unsafe { &raw mut (*fields).rank };
        let new_rank = if left_rank >= right_rank {
            right_rank + 1
        } else {
            unsafe {
                (&raw mut (*fields).a).write(right);
                (&raw mut (*fields).b).write(left);
            }
            left_rank + 1
        };
        if STOP_ON_UNCHANGED && unsafe { rank_slot.read() } == new_rank {
            break;
        }
        unsafe { rank_slot.write(new_rank) };
        node = unsafe { (&raw const (*fields).parent).read() };
        *steps += 1;
    }
}

/// Remove the minimum node and write it to the caller's output slot.
///
/// # Safety
///
/// `root` points to a nonempty heap. `removed` may alias `root`. C owns the
/// queue and gives this call exclusive access. Layout and counter pointers
/// satisfy the insertion contract above.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_timeout_queue_delete_min(
    root: *mut *mut c_void,
    removed: *mut *mut c_void,
    empty: *mut c_void,
    parent_offset: usize,
    merge_count: *mut c_int,
    leftify_count: *mut c_int,
) {
    let old_root = unsafe { root.read() };
    let fields = unsafe { suffix(old_root, parent_offset) };
    let left = unsafe { (&raw const (*fields).a).read() };
    let right = unsafe { (&raw const (*fields).b).read() };
    unsafe {
        (&raw mut (*fields).a).write(empty);
        (&raw mut (*fields).b).write(empty);
        removed.write(old_root);
    }
    let mut merge_steps = 0;
    let mut leftify_steps = 0;
    let lowest = unsafe {
        merge_down(
            left,
            right,
            empty,
            root,
            empty,
            parent_offset,
            &mut merge_steps,
        )
    };
    unsafe { leftify::<false>(lowest, empty, empty, parent_offset, &mut leftify_steps) };
    if !merge_count.is_null() {
        unsafe { *merge_count += merge_steps };
    }
    if !leftify_count.is_null() {
        unsafe { *leftify_count += leftify_steps };
    }
}

/// Remove one member and leave its parent and children set to EMPTY.
///
/// # Safety
///
/// `member` belongs to `root`. C owns the queue and gives this call
/// exclusive access. Layout and counter pointers satisfy the insertion
/// contract above.
#[unsafe(no_mangle)]
pub(super) unsafe extern "C" fn ghc_rust_timeout_queue_delete(
    root: *mut *mut c_void,
    member: *mut c_void,
    empty: *mut c_void,
    parent_offset: usize,
    merge_count: *mut c_int,
    leftify_to_count: *mut c_int,
    leftify_shortcut_count: *mut c_int,
) {
    let fields = unsafe { suffix(member, parent_offset) };
    let left = unsafe { (&raw const (*fields).a).read() };
    let right = unsafe { (&raw const (*fields).b).read() };
    let parent = unsafe { (&raw const (*fields).parent).read() };
    unsafe {
        (&raw mut (*fields).a).write(empty);
        (&raw mut (*fields).b).write(empty);
        (&raw mut (*fields).parent).write(empty);
    }
    let parent_child = if parent == empty {
        root
    } else {
        let parent_fields = unsafe { suffix(parent, parent_offset) };
        let parent_left = unsafe { (&raw const (*parent_fields).a).read() };
        if parent_left == member {
            unsafe { &raw mut (*parent_fields).a }
        } else {
            unsafe { &raw mut (*parent_fields).b }
        }
    };
    let mut merge_steps = 0;
    let mut leftify_to_steps = 0;
    let mut shortcut_steps = 0;
    let lowest = unsafe {
        merge_down(
            left,
            right,
            parent,
            parent_child,
            empty,
            parent_offset,
            &mut merge_steps,
        )
    };
    unsafe {
        leftify::<false>(lowest, parent, empty, parent_offset, &mut leftify_to_steps);
        leftify::<true>(parent, empty, empty, parent_offset, &mut shortcut_steps);
    }
    if !merge_count.is_null() {
        unsafe { *merge_count += merge_steps };
    }
    if !leftify_to_count.is_null() {
        unsafe { *leftify_to_count += leftify_to_steps };
    }
    if !leftify_shortcut_count.is_null() {
        unsafe { *leftify_shortcut_count += shortcut_steps };
    }
}
