# Rust RTS handoff · 28 November 2026

Work is paused. The last runtime commit is `0d6403909c`. The branch is `rust-rts` on `TharkunAB/ghc`. It targets native x86-64 GNU/Linux with Rust 1.100.0. The mixed RTS is opt-in with `./configure --enable-rust-rts`. [Pull request #2](https://github.com/TharkunAB/ghc/pull/2) · [Port roadmap](docs/rts/rust-port-roadmap.md)

## What passed

| Runtime revision | Change | Verification |
| --- | --- | --- |
| `937d12fae8` | Rust owns pending foreign exports and the current loading object. | The full stage2 build passed. Generated exports, reentrant registration, GC and unloading preserved root order and ownership. |
| `26f5f382d1` | Rust sweeps per-capability mutable lists. C allocates blocks on rollover. | The full stage2 build passed after the timed pause. The persistent worker handled 169 Haskell compilations. All eight installed RTS libraries matched their build outputs. Tiny and Fibonacci passed in vanilla static, threaded static and dynamic programs. |
| `6d4129f9be`, `0d6403909c` | Rust walks the debug CAF snapshot and clears whole free nonmoving segments. | The registered RTS at the combined tip passed. The debug CAF check verified visit order, dead stubs, locked reattachment and snapshot reset. The threaded-release clear checked 1,936 segments of 32 KiB each. Full stage2 qualification at this tip is **pending**. |

Rust covers at least one operation in 50 of 180 baseline C files. Complete C files by static build are 20 threaded release, 19 vanilla, 18 threaded debug and 16 nonthreaded debug. Cmm has one partially ported file and zero complete files out of 17. Keep C first.

## Open correctness work

1. **Compact weak keys and stable names.** On stock GHC 9.14.1, hold a compact list alive with a stable pointer to the compact handle. Force a tail in an interior block, give it a weak pointer and stable name, then perform two blocking major collections. The tail is still readable at the same address, but the weak pointer is empty and the new stable name differs. The ordinary-list control passes. Native moving-GC `isAlive` returned null for the interior pointer while the owner descriptor carried the live flag. Both copying and nonmoving runs reproduce this. Test looking up the owner's descriptor while returning the original tagged pointer. Also check that an unreachable region loses its weak reference and its finalizer runs. The nonmoving weak-key and stable-name paths may also need owner-aware checks. Commit the regression and confirmed C correction first, then match it in Rust. [C liveness](rts/sm/GCAux.c) · [Nonmoving marking](rts/sm/NonMovingMark.c) · [Rust liveness](rts/rust/liveness.rs)
2. **Intermittent debug mark-queue assertion.** Before the whole-segment clear port, the uninstrumented `rts_clearMemory` test failed at `NonMovingMark.c:534` in 2/10 mixed runs. All ten interleaved runs with the same revision's C sweep fallback passed. A second control that replaced only free-block clearing still failed (2/12 versus 3/12 mixed). The cause remains open. Isolate segment sweeping and publication next. [Public test](testsuite/tests/ffi/should_run/rts_clearMemory_c.c)

## Restart after the pause

Start with full stage2 qualification of `0d6403909c`. On Matti's WSL host, the checkout is `/home/tritlo/Code/rust-rts`. The retained incremental and stage2 build trees are under `/tmp/ghc-rust-rts-incremental-RVBr` and `/tmp/ghc-rust-rts-stage2-reuse`. If the latter is still present, this submits one managed build using the persistent worker.

```bash
cd /home/tritlo/Code/rust-rts
env -u XDG_RUNTIME_DIR RUST_LOG=error bash /tmp/ghc-rust-rts-stage2-reuse/submit.sh \
  --local-checkout "$PWD" 0d6403909c364d67c1dd63bca528b23a1a7f9123
```

Check the returned Pueue job, its exit code and the stage2 tree's `qualified-revision`. Compare the witnesses before changing code. If retained, the stock native traces are under `/tmp/ghc-rust-compact-liveness/stock-914-trace`, and the assertion backtrace is under `/tmp/ghc-rust-segment-debug-isolation/baseline/gdb-4.log`. These host-local paths are temporary.
