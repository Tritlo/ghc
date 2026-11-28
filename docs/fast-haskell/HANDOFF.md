# Incremental GHC self-build handoff

28 November 2026. Scope is GHC 10 development rebuild latency on this
host. Final builds use ordinary GHC and leave the development options unset.

## Branches and active tools

| Checkout | Branch and state |
| --- | --- |
| `/home/tritlo/Code/incremental-builds` | `TharkunAB/ghc:incremental-builds`. The performance report through the v4 switch is in `e4ca07f401`. |
| `/home/tritlo/Code/ghc-persistent-worker-incremental` | Local worker fork, `incremental-builds` at `de40d41`. The released code is `94c0f01`. The later commit records activation in `CHANGELOG.md`. |
| `/home/tritlo/Code/ghc-persistent-worker/_build/stage0-bin/current` | Active Stage0 v4 worker `94c0f01`. Its underlying compiler is GHC 10.1.20261127, executable SHA-256 prefix `cafe7121a8e6`. |
| `/home/tritlo/Code/ghc-persistent-worker/_build/current` | Stage1 worker `fd8d51d`, for GHC 10.1.20261115.1. |

## What is measured

- The linked `-O2` `GHC.Utils.Misc` edit and revert took **152.43 s →
  53.12 s (2.87×)** from the starting configuration to the published
  development configuration. Each configuration ran one edit and one
  revert using the same compiler executable. The importer rule reduced
  compile requests from 303 to 54 per edit. The checked artifacts and a
  fresh dynamic GHC API consumer matched ordinary GHC.
- On the exact 943-module dependency command, Stage0 v4 reduced
  median admission into a nearly full cache from **6.327 s to
  5.787 s** across four alternating pairs. Ordinary GHC took a
  **10.646 s** median from two runs. Median fresh restart after
  admission fell from **4.308 s to 3.964 s**. The packaged shim and daemon
  matched the measured hashes. The optional positive CPP cache uses a
  mode-0700 directory and fills its own v4 file.
- The linked baseline comparison predates two later changes, concurrent
  Stage1 package copy and ABI calculation and the v4 worker. The separate
  timings in [PERFORMANCE.md](PERFORMANCE.md) cover different build
  configurations. The project has no measured clean-build speedup.

## Worker checkpoint

Pueue 7551 checked the exact 943-module scan on ordinary GHC, the
released worker and a worker with phase timestamps. Outputs and
diagnostics matched throughout. The instrumented fresh restart spent
2.258 s in dependency analysis, 0.602 s in its initial file-plan
checkpoint, and 0.801 s rendering rows and collecting headers. The
GCC configuration probes accounted for 25.7 ms in total. Each state
has one observation.

Pueue 7555 compared the old and new CPP directive scanners. It passed
299,593 generated short byte strings, 3,744 boundary cases, 26 explicit
cases, five large cases and 881 real source inputs. The candidate
visits only lines that contain a possible directive and retains the
existing byte checks, splice handling and directive parser. It still
needs a matched full dependency timing before any release decision.

The data and candidate source are under
`/home/tritlo/Code/ghc/_build/fast-haskell/portable-normalized-interfaces/dependency-restart-next`.
Use `phase-replay-7551/REPORT.md` for trace results and
`directive-scan-7555/directive-scan.patch` for the scanner candidate
against `de40d41`. Each directory has an evidence checksum manifest.

## Hadrian archive checkpoint

Pueue 7485 measured one matched forward edit at **18.494 s →
16.405 s** with one of 883 archive members re-stripped. The checked
artifacts and fresh dynamic consumer matched. Its reverse edit
re-stripped all 883 members and stopped at the reuse assertion. A
separate probe showed that an overlay remount can change every cached
product's device identifier while preserving inode, size, and the
sampled file's bytes.

The repaired candidate retains the cheap stamp check and stores each
stripped product's SHA-256. A stamp mismatch triggers a content check.
Jobs 7552 and 7553 built the private driver and prepared both arms.
The candidate stripped all 883 members on first fill and one on the
prepared edit. Preparation kept package copy and ABI calculation
overlapping. The final timed job 7554 was stopped at the pause. A
complete comparison with a forced remount remains pending.

Under the evidence root, `native-strip-hadrian/linked-7485` holds the
first comparison and standalone fallback tests.
`native-strip-hadrian/linked-7554` holds the repaired patch, source
archive, replay scripts, preparation results and partial timing logs.
Verify `evidence.sha256` before unpacking. The candidate is scoped to
the exact GNU binutils used on this x86-64 Linux host.

## Resume

1. Start with the worker scanner's full dependency comparison. Compare
   the exact candidate binaries with the active v4 release and its
   underlying ordinary GHC. Keep an activation report and update the
   changelog if the shared selector changes.
2. Recreate the private Hadrian capsule from the archived replay and
   rerun the two-direction linked comparison. Check that the forced
   remount reuses unchanged products and that stale receipts and strip
   errors follow the ordinary path.
3. Keep the two lanes in the existing fair Pueue groups. Use ordinary
   GHC for final builds. Retain receipts in the evidence root and prune
   each completed capsule from `/tmp`.

All jobs from this batch finished or were stopped before the pause.
The active Stage0 and Stage1 selectors are recorded above.
