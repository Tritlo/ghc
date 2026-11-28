use core::ffi::c_void;
use core::ptr::null_mut;
use core::sync::atomic::{AtomicPtr, Ordering};

core::arch::global_asm!(
    ".hidden ghc_rust_collect_dead_weak_generations",
    ".hidden ghc_rust_mark_weak_generations",
    ".hidden ghc_rust_collect_fresh_weaks",
    ".hidden ghc_rust_init_weak_generations",
    ".hidden ghc_rust_traverse_weaks",
    ".hidden ghc_rust_resurrect_thread_generations",
    ".hidden ghc_rust_scavenge_live_weak",
    ".hidden ghc_rust_tidy_weak_generations",
    ".hidden ghc_rust_tidy_thread_generations",
);

unsafe extern "C" {
    fn mark_root(gc_thread: *mut c_void, slot: *mut *mut u8);
    fn ghc_rust_mark_weak_roots(
        worker: *mut c_void,
        value: *mut *mut u8,
        key: *mut *mut u8,
        finalizer: *mut *mut u8,
        cfinalizers: *mut *mut u8,
    );
    static stg_NO_FINALIZER_closure: u8;
    static stg_DEAD_WEAK_info: u8;
}

#[repr(C)]
struct WeakPayload {
    cfinalizers: *mut u8,
    key: *mut u8,
    value: *mut u8,
    finalizer: *mut u8,
    link: *mut u8,
}

// The caller can be the main collector or a worker scavenging a mutable list.
#[unsafe(no_mangle)]
unsafe extern "C" fn ghc_rust_scavenge_live_weak(
    weak: *mut u8,
    worker: *mut c_void,
    payload_offset: usize,
) {
    unsafe {
        let payload = weak.add(payload_offset).cast::<WeakPayload>();
        ghc_rust_mark_weak_roots(
            worker,
            &raw mut (*payload).value,
            &raw mut (*payload).key,
            &raw mut (*payload).finalizer,
            &raw mut (*payload).cfinalizers,
        );
    }
}

#[repr(C)]
struct WeakList {
    head: *mut u8,
    tail: *mut u8,
}

// See Note [Weak generation traversal from Rust] in sm/MarkWeak.c.
#[repr(C)]
struct WeakGenerations {
    generations: *mut u8,
    stride: usize,
    old_threads_offset: usize,
    live_weaks_offset: usize,
    old_weaks_offset: usize,
    number_offset: usize,
    collected: u32,
    oldest: u32,
    nonmoving: bool,
}

#[repr(C)]
struct WeakStageLayout {
    stride: usize,
    old_threads_offset: usize,
    live_weaks_offset: usize,
    old_weaks_offset: usize,
    number_offset: usize,
    weak_payload_offset: usize,
    tso_link_offset: usize,
    tso_what_next_offset: usize,
    end_tso: *mut u8,
    killed: u16,
    complete: u16,
    inspect_tso: unsafe extern "C" fn(*mut *mut u8) -> *mut *mut u8,
    weak_ops: *const WeakListOps,
    check_oldest: Option<unsafe extern "C" fn(*mut *mut u8)>,
}

#[repr(C)]
struct WeakStageRun {
    generations: *mut u8,
    collected: u32,
    oldest: u32,
    nonmoving: bool,
    worker: *mut c_void,
    dead: *mut *mut u8,
    resurrected: *mut *mut u8,
    evac_gen: *mut u32,
    failed: *mut bool,
    oldest_old_slot: *mut *mut u8,
}

unsafe fn tidy_live_keys(
    layout: &WeakStageLayout,
    run: &WeakStageRun,
    generations: &WeakGenerations,
) -> bool {
    unsafe {
        if run.nonmoving && run.oldest <= run.collected {
            if let Some(check) = layout.check_oldest {
                check(run.oldest_old_slot);
            }
        }
        ghc_rust_tidy_weak_generations(generations, run.worker, run.evac_gen,
            run.failed, layout.weak_payload_offset, layout.weak_ops)
    }
}

#[repr(C)]
struct WeakListOps {
    live_key: unsafe extern "C" fn(*mut u8, *const u8) -> *mut u8,
    destination: unsafe extern "C" fn(*mut u8, *mut u32) -> *mut *mut u8,
    remember: unsafe extern "C" fn(*mut c_void, *mut u8, u32),
    trace: Option<unsafe extern "C" fn(*mut u8, u32, u32)>,
}

// This pass runs after scavenging stops. Move live weak objects to their owning generations.
unsafe fn tidy_weak_list(
    mut previous: *mut *mut u8,
    from: u32,
    worker: *mut c_void,
    evac_gen: *mut u32,
    failed: *mut bool,
    payload_offset: usize,
    ops: *const WeakListOps,
) -> bool {
    unsafe {
        let mut found = false;
        let mut weak = previous.read();
        while !weak.is_null() {
            let payload = weak.add(payload_offset).cast::<WeakPayload>();
            let link = &raw mut (*payload).link;
            let info = weak.cast::<*const u8>().read();
            if info == &raw const stg_DEAD_WEAK_info {
                weak = link.read();
                previous.write(weak);
                continue;
            }
            let key = ((*ops).live_key)(weak, info);
            if key.is_null() {
                previous = link;
                weak = link.read();
                continue;
            }

            (*payload).key = key;
            let mut to = 0;
            let destination = ((*ops).destination)(weak, &raw mut to);
            evac_gen.write(to);
            failed.write(false);
            ghc_rust_scavenge_live_weak(weak, worker, payload_offset);
            if failed.read() {
                ((*ops).remember)(worker, weak, to);
            }

            let next = link.read();
            previous.write(next);
            link.write(destination.read());
            destination.write(weak);
            if let Some(trace) = (*ops).trace {
                trace(weak, from, to);
            }
            found = true;
            weak = next;
        }
        found
    }
}

#[unsafe(no_mangle)]
unsafe extern "C" fn ghc_rust_tidy_weak_generations(
    generations: *const WeakGenerations,
    worker: *mut c_void,
    evac_gen: *mut u32,
    failed: *mut bool,
    payload_offset: usize,
    ops: *const WeakListOps,
) -> bool {
    unsafe {
        let layout = &*generations;
        let mut found = false;
        for index in 0..=layout.collected {
            if layout.nonmoving && index == layout.oldest {
                continue;
            }
            let generation = layout.generations.add(index as usize * layout.stride);
            let old = generation.add(layout.old_weaks_offset).cast::<*mut u8>();
            let from = generation.add(layout.number_offset).cast::<u32>().read();
            found |= tidy_weak_list(old, from, worker, evac_gen,
                failed, payload_offset, ops);
        }
        found
    }
}

// See Note [Tidy thread list ownership] in sm/MarkWeak.c.
unsafe fn tidy_thread_list(
    old: *mut *mut u8,
    end: *mut u8,
    link_offset: usize,
    inspect: unsafe extern "C" fn(*mut *mut u8) -> *mut *mut u8,
) {
    unsafe {
        let mut previous = old;
        let mut tso = old.read();
        while tso != end {
            let destination = inspect(&raw mut tso);
            let link = tso.add(link_offset).cast::<*mut u8>();
            let next = link.read();
            if destination.is_null() {
                previous = link;
            } else {
                previous.write(next);
                link.write(destination.read());
                destination.write(tso);
            }
            tso = next;
        }
    }
}

#[unsafe(no_mangle)]
unsafe extern "C" fn ghc_rust_tidy_thread_generations(
    generations: *const WeakGenerations,
    end: *mut u8,
    link_offset: usize,
    inspect: unsafe extern "C" fn(*mut *mut u8) -> *mut *mut u8,
) {
    unsafe {
        let layout = &*generations;
        for index in 0..=layout.collected {
            let generation = layout.generations.add(index as usize * layout.stride);
            let old = generation.add(layout.old_threads_offset).cast::<*mut u8>();
            tidy_thread_list(old, end, link_offset, inspect);
        }
    }
}

#[derive(Clone, Copy)]
enum WeakStage {
    Threads,
    Pointers,
    Done,
}

// Only the main GC thread reads or changes the stage during a collection.
static mut WEAK_STAGE: WeakStage = WeakStage::Pointers;

#[unsafe(no_mangle)]
unsafe extern "C" fn ghc_rust_traverse_weaks(
    layout: *const WeakStageLayout,
    run: *const WeakStageRun,
) -> bool {
    unsafe {
        let layout = &*layout;
        let run = &*run;
        let generations = WeakGenerations {
            generations: run.generations,
            stride: layout.stride,
            old_threads_offset: layout.old_threads_offset,
            live_weaks_offset: layout.live_weaks_offset,
            old_weaks_offset: layout.old_weaks_offset,
            number_offset: layout.number_offset,
            collected: run.collected,
            oldest: run.oldest,
            nonmoving: run.nonmoving,
        };
        match WEAK_STAGE {
            WeakStage::Done => return false,
            WeakStage::Threads => {
                ghc_rust_tidy_thread_generations(&raw const generations,
                    layout.end_tso, layout.tso_link_offset, layout.inspect_tso);
                if tidy_live_keys(layout, run, &generations) {
                    return true;
                }
                let resurrected = ghc_rust_resurrect_thread_generations(
                    &raw const generations, run.resurrected, run.worker,
                    layout.end_tso, layout.tso_link_offset, layout.tso_what_next_offset,
                    layout.killed, layout.complete);
                WEAK_STAGE = WeakStage::Pointers;
                if resurrected {
                    return true;
                }
            }
            WeakStage::Pointers => {}
        }
        if !tidy_live_keys(layout, run, &generations) {
            ghc_rust_collect_dead_weak_generations(
                run.generations, layout.stride, layout.old_weaks_offset,
                run.collected, run.dead, run.worker, layout.weak_payload_offset);
            WEAK_STAGE = WeakStage::Done;
        }
        // The collector must scavenge the roots reached by the last pass.
        true
    }
}

// See Note [Weak pointer processing and the non-moving GC] in sm/MarkWeak.c.
#[unsafe(no_mangle)]
unsafe extern "C" fn ghc_rust_init_weak_generations(
    generations: *mut u8,
    stride: usize,
    live_offset: usize,
    old_offset: usize,
    collected: u32,
    oldest: u32,
    nonmoving: bool,
) {
    unsafe {
        for index in 0..=collected {
            if nonmoving && index == oldest {
                break;
            }
            let generation = generations.add(index as usize * stride);
            let live = generation.add(live_offset).cast::<*mut u8>();
            let old = generation.add(old_offset).cast::<*mut u8>();
            old.write(live.read());
            live.write(null_mut());
        }
        WEAK_STAGE = WeakStage::Threads;
    }
}

// Each capability contributes one list, in ascending capability order.
#[unsafe(no_mangle)]
unsafe extern "C" fn ghc_rust_collect_fresh_weaks(
    nursery: *mut *mut u8,
    caps: *mut *mut u8,
    count: u32,
    endpoints_offset: usize,
    payload_offset: usize,
    check: Option<unsafe extern "C" fn(*mut u8, *mut u8)>,
) {
    unsafe {
        for i in 0..count as usize {
            let cap = AtomicPtr::from_ptr(caps.add(i)).load(Ordering::Relaxed);
            let list = cap.add(endpoints_offset).cast::<WeakList>();
            let head = (*list).head;
            let tail = (*list).tail;
            if let Some(check) = check {
                check(head, tail);
            }
            if !tail.is_null() {
                let payload = tail.add(payload_offset).cast::<WeakPayload>();
                (*payload).link = nursery.read();
                nursery.write(head);
                (*list).tail = null_mut();
                (*list).head = null_mut();
            }
        }
    }
}

// Evacuation can replace the object in the root slot. Follow the link in its new location.
#[unsafe(no_mangle)]
unsafe extern "C" fn ghc_rust_mark_weak_generations(
    generations: *const WeakGenerations,
    worker: *mut c_void,
    payload_offset: usize,
    check: Option<unsafe extern "C" fn(*mut u8)>,
) {
    unsafe {
        // The oldest nonmoving generation keeps its live weak list. Mark it too.
        let layout = &*generations;
        for index in 0..=layout.collected {
            let generation = layout.generations.add(index as usize * layout.stride);
            let mut slot = generation.add(layout.live_weaks_offset).cast::<*mut u8>();
            loop {
                let weak = AtomicPtr::from_ptr(slot).load(Ordering::Relaxed);
                if weak.is_null() {
                    break;
                }
                if let Some(check) = check {
                    check(weak);
                }
                mark_root(worker, slot);
                let moved = slot.read().add(payload_offset).cast::<WeakPayload>();
                slot = &raw mut (*moved).link;
            }
        }
    }
}

// Keep the original next link before marking. The root slot can move a live TSO.
unsafe fn resurrect_unreachable_threads(
    old: *mut *mut u8,
    resurrected: *mut *mut u8,
    gc_thread: *mut c_void,
    end: *mut u8,
    link_offset: usize,
    what_next_offset: usize,
    killed: u16,
    complete: u16,
) -> bool {
    unsafe {
        let mut tso = old.read();
        let mut found = false;
        while tso != end {
            let link = tso.add(link_offset).cast::<*mut u8>();
            let next = link.read();
            let what_next = tso.add(what_next_offset).cast::<u16>().read();
            if what_next == killed || what_next == complete {
                link.write(end);
            } else {
                let mut moved = tso;
                mark_root(gc_thread, &raw mut moved);
                moved
                    .add(link_offset)
                    .cast::<*mut u8>()
                    .write(resurrected.read());
                resurrected.write(moved);
                found = true;
            }
            tso = next;
        }
        old.write(end);
        found
    }
}

#[unsafe(no_mangle)]
unsafe extern "C" fn ghc_rust_resurrect_thread_generations(
    generations: *const WeakGenerations,
    resurrected: *mut *mut u8,
    gc_thread: *mut c_void,
    end: *mut u8,
    link_offset: usize,
    what_next_offset: usize,
    killed: u16,
    complete: u16,
) -> bool {
    unsafe {
        let layout = &*generations;
        let mut changed = false;
        for index in 0..=layout.collected {
            let generation = layout.generations.add(index as usize * layout.stride);
            let old = generation.add(layout.old_threads_offset).cast::<*mut u8>();
            changed |= resurrect_unreachable_threads(
                old, resurrected, gc_thread, end, link_offset, what_next_offset, killed, complete,
            );
        }
        changed
    }
}

// See Note [Visiting dead weak pointers from Rust] in sm/MarkWeak.c.
unsafe fn collect_dead_weaks(
    mut weak: *mut u8,
    pending: *mut *mut u8,
    gc_thread: *mut c_void,
    payload_offset: usize,
) {
    unsafe {
        while !weak.is_null() {
            let payload = weak.add(payload_offset).cast::<WeakPayload>();
            if (*payload).cfinalizers.cast_const() != &raw const stg_NO_FINALIZER_closure {
                mark_root(gc_thread, &raw mut (*payload).value);
            }
            mark_root(gc_thread, &raw mut (*payload).finalizer);
            let next = (*payload).link;
            (*payload).link = pending.read();
            pending.write(weak);
            weak = next;
        }
    }
}

// Visit each collected generation's old weak list in generation order.
#[unsafe(no_mangle)]
unsafe extern "C" fn ghc_rust_collect_dead_weak_generations(
    generations: *mut u8,
    stride: usize,
    old_offset: usize,
    collected: u32,
    pending: *mut *mut u8,
    gc_thread: *mut c_void,
    payload_offset: usize,
) {
    unsafe {
        for index in 0..=collected {
            let generation = generations.add(index as usize * stride);
            let old = generation.add(old_offset).cast::<*mut u8>().read();
            collect_dead_weaks(old, pending, gc_thread, payload_offset);
        }
    }
}
