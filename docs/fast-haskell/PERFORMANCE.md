# Incremental GHC self-builds

Use ordinary GHC for final builds. At each development-worker switch, compare with the exact GHC executable behind that worker. At each GHC or RTS switch, use an unmodified build of the same source revision, flavour and toolchain. Record revisions, workload, sample count, results and the reason for the switch. Include memory for changes that retain data or change the heap. Each worker release keeps its own `PERFORMANCE.md`.

## 27 November 2026

### Published importer rule on GHC 10.1.20261127

The original Hadrian `56bb91d95f` used ordinary GHC. The optimized build used the published Hadrian rule, one Hadrian capability, and a warm `e0d203b` worker for dependency scans and compile checks. Both used the same Stage0 executable (SHA-256 prefix `cafe7121a8e6`), `perf+no_profiled_libs --freeze1 -j3`, and logical CPUs 20–23. Both targeted `stage2:exe:ghc-bin` and used the default compiler nursery.

| Linked `-O2` rebuild | Original Hadrian | Published importer rule |
| --- | ---: | ---: |
| Change cutoff 32 to 31 | 76.75 s | 25.21 s (3.04×) |
| Immediate repeat | 33.37 s | 4.14 s |
| Revert 31 to 32 | 75.68 s | 27.91 s (2.71×) |
| Immediate repeat | 25.57 s | 5.05 s |

The edit and revert together took **152.43 s with the original build and 53.12 s with the optimized build (2.87×, 65.1% less time)**. The optimized build issued 54 compile requests per edit instead of 303 and regenerated one of 943 dependency rows. Only the edited producer generated code. The checked module artifacts, package archive, shared library, linked compiler and separately compiled dynamic API consumer matched ordinary GHC. Every immediate repeat ran zero build actions.

Separate writable overlays used the same read-only build. Preparation and worker warm-up took place before each stopwatch interval. Each cell is one sample. After correcting the primer, the original windows ran before the optimized windows. Pueue recorded overlap with a small-group task in the original forward window and a build-group task in the optimized reverse window. Whole-job memory peaks were 2,548 and 2,491 MiB for the original windows and 3,425 and 3,504 MiB for the optimized windows, including worker warm-up and verification.

### Linker choice on the published development route

With the same optimized Hadrian rules, Stage0 `cafe7121a8e6` and worker `df96e32`, we compared GNU BFD 2.42 and mold 2.30.0. Both used `perf+no_profiled_libs --freeze1 -j3`, the default compile nursery and logical CPUs 20–23. The link flags applied to the Stage1 compiler library and executable. Worker warm-up and verification ran outside the timed edit. The forward pair ran BFD first. The reverse pair ran mold first.

| Linked `-O2` rebuild | BFD | mold |
| --- | ---: | ---: |
| Change cutoff 32 to 31 | 26.644 s | 19.683 s |
| Immediate repeat | 4.650 s | 4.778 s |
| Revert 31 to 32 | 28.255 s | 19.579 s |
| Immediate repeat | 4.064 s | 4.137 s |

The two edits took **54.899 s with BFD and 39.262 s with mold (1.40×, 28.5% less time)**. Each edit ran 54 compile requests, skipped 53 code generations and regenerated one of 943 dependency rows. Every immediate repeat did zero builder actions. Each cell is one sample. Whole-job memory peaks were 4,290 and 4,538 MiB for the two paired windows, including warm-up and validation.

Module artifacts, dependency files, compiler archives and the consumer's object and interface matched. The shared libraries had the same exported symbol descriptions, ordered library dependencies, runpath and library name. Each compiler and consumer loaded its newly linked library through the default loader and the consumer returned the same result. [Linker flags](rebuild-c33551f.md#fix-for-the-repeated-package-copy)

### Cumulative comparison on GHC 10.1.20261127

We built Hadrian from the branch point `56bb91d95f` and used ordinary GHC for both dependency scanning and compilation. The development configuration used the published Hadrian changes, one Hadrian capability, and a stage-matched worker for dependency scans and compile checks with its decoded-interface cache enabled. The pilot also used an importer's actual source options and interface usage records to decide whether a change to `GHC.Utils.Misc` required a compiler call. Hadrian still passed changed code to the ordinary compiler and relinked its library and executable.

| Linked `-O2` rebuild | Starting Hadrian + ordinary GHC | Published development options | Automatic importer pilot |
| --- | ---: | ---: | ---: |
| Change cutoff 32 to 31 | 63.46 s | 30.65 s (2.07×) | 26.36 s (2.41×) |
| Revert 31 to 32 | 59.70 s | 33.85 s (1.76×) | 25.90 s (2.31×) |
| No-op after forward edit | 23.54 s | 4.00 s | 3.82 s |
| No-op after revert | 23.95 s | 4.43 s | 3.85 s |

Across the edit and revert together, the published options cut wall time by 47.6% (1.91×). The pilot cut it by 57.6% (2.36×).

Each cell is one run on the same previously built source tree, native Stage0 compiler, four CPUs, `-j3`, and `perf+no_profiled_libs --freeze1`. All arms ran the normal `stage2:exe:ghc-bin` target. The starting compiler executable was held constant so these comparisons measure the build system and worker. The development worker was warm. It regenerated one of 943 dependency rows on each edit. The starting configuration ran an ordinary dependency scan. The development and pilot windows ran before the branch-point control, so the ratios include run-to-run noise.

The starting and published configurations ran 303 Haskell compile commands. The pilot ran 54. Only the edited producer generated code. The module artifacts of all 249 skipped importers, the compiler archive, shared library, compiler executable, and a separately compiled and executed GHC API consumer matched the ordinary reference. Each immediate no-op ran zero builder actions. The two separate starting benchmark jobs peaked at 2,564 and 2,578 MiB in their cgroups. The two-direction worker and pilot jobs peaked at 5,772 and 4,680 MiB. These are whole-job peaks, including the compiler and resident workers.

### Private Stage0 cache for CPP dependencies

The exact shared Stage0 CLI (`cafe7121a8e6`) ran the same 943-module
dependency scan as a private worker built with three replacement GHC API
objects. With fresh worker daemons and both disk caches populated, the
worker took **4.793 s with the existing cache and 3.466 s with the
CPP dependency cache added** (27.7% less time over four alternating pairs).
Both arms reused 835 empty certificates. The opt-in arm also reused all
104 CPP records and still ran normal preprocessing. The Makefile, backup
and diagnostics matched stock GHC. The 1,068 watched inputs were stable.
Stock GHC took 7.582 s and the installed `2baf1e8` worker took 4.506 s
with its existing cache in separate single controls.

A separate build against the ordinary toolchain omitted the new cache
capability and passed the dependency, compile-check and fallback smoke
tests. Pueue jobs 7211 and 7214 collected these results. The optimized
worker used a private API overlay. This experiment preceded qualification
of the packaged Stage0 release.

### CPP cache across temporary directories

On the exact 943-module Stage0 command, a worker seeded its cache under
one temporary directory and restarted under four longer paths. The
released worker reused zero of 104 CPP records in each new directory.
The candidate reused all 104 by hashing the bytes around the proven
generated header marker and checking the current ordinary marker paths.
The median fell from **5.371 s to 3.943 s** (26.6%) over four alternating
pairs. Both reused 835 empty certificates and matched stock dependency
files, backups and diagnostics. Stock controls in two directories had a
median of 8.745 s. All 1,068 watched inputs stayed stable.

The candidate missed when a different temporary prefix made an ordinary
header eligible. It also matched stock on parser warnings, CPP failure
and escaped temporary paths. A separate fixture reused a receipt after
crossing from a two-digit process ID to four digits in one directory.
Pueue jobs 7286 and 7292 verified the private candidate. The paired job
peaked at 547 MiB.

The packaged worker `8a03b68` is now the shared Stage0 release on the same
GHC executable. Four alternating fresh-daemon pairs with changed
temporary directories took **5.373 s with `ad8a24f` and 3.886 s with
`8a03b68`** (27.7% less time). Stock controls took 10.144 s and 12.847 s.
In the original temporary directory, one control per worker took 4.626 s
and 4.756 s respectively. Both workers reused all 104 CPP records there.
The packaged worker passed compile-check, fallback and diagnostic smoke.
All 943-module outputs matched stock, and the timing job peaked at
552 MiB (Pueue 7302). Use an existing mode-0700 directory with
`GHC_WORKER_POSITIVE_CPP_CACHE` to enable the version-2 store.

### Cabal compiler-library installation

We replayed the complete Stage1 GHC package copy with the original Cabal
3.16.0.0 setup configuration and built libraries. Both timed arms used
the same private Cabal executable and the same strip program. Changing
the atomic copy buffer from 4 KiB to 128 KiB reduced the median from
**4.188 s to 3.921 s** (6.4%) across four alternating pairs. It saved
0.236–0.288 s per run. All 1,763 installed files matched ordinary Cabal
in bytes and permissions, including the stripped archive and shared
library. Diagnostics also matched.

An untimed I/O check measured about 61,600 fewer read calls and 61,600
fewer write calls. Pueue job 7210 used logical CPUs 20–23 and a 4 GiB
cap. This was a private library install replay. The linked-build
measurements use the existing Cabal copy code.

A separate experiment let GNU strip 2.42 read the built archive and
shared library directly and write to temporary files in the installation
directory. Cabal then set the normal modes and renamed the files. Skipping
the intermediate copies reduced the complete copy step from **4.414 s to
3.700 s** (16.2%) across four alternating pairs. The original 4 KiB buffer
was in use in both arms. Pueue job 7233 verified the direct calls, all
1,763 installed files, diagnostic output and parity under umask 077. The
prototype is private and the timings cover the install step alone.

On the linked Stage2 compiler target, the direct-strip edit took 19.431 s
versus 21.639 s with ordinary Cabal. The revert took 21.156 s versus
20.270 s. The total fell from **41.909 s to 40.587 s** (3.2%, one sample
per cell). Both modes used the same Hadrian executable, persistent
arguments, worker `2baf1e8` and mold. A separate trace verified direct
strip for the archive and shared library. Each edit ran 54 compiler
requests and generated code for one module. Every immediate repeat ran
zero builders. All 1,763 installed files, the package database, the
linked compiler and the dynamic API consumer matched. Direct strip
remains an experiment. Pueue job 7268 peaked at 4,325 MiB.

### Overlap compiler package copy and ABI calculation

The package registration replay used the exact Cabal copy driver and
the captured 880-module Stage0 ABI command. Both modes used the
direct-strip prototype. Running copy and ABI calculation concurrently
reduced the median copy-to-recache time from **5.903 s to 4.374 s**
(25.9%) across four alternating pairs. Every concurrent pair improved.
The replay wrote the retained package configuration after the computed
ABI matched. It then ran the usual recache. All 1,765 output files
matched in bytes and mode, including the registration and package cache.
Diagnostics matched. Pueue job 7290 peaked at 1,406 MiB.
These timings cover the registration phase outside Hadrian.


The linked Hadrian comparison used stock Cabal 3.16.0.0, Stage0
`cafe7121a8e6`, worker `2baf1e8`, mold, persistent arguments and one
Hadrian capability. Both modes used the same Hadrian executable and ran
`perf+no_profiled_libs --freeze1 -j3 stage2:exe:ghc-bin` on logical CPUs
20–23. The forward pair ran sequential registration first. The revert
pair ran concurrent registration first. Only the separate preparation
runs used Shake profiling.

| Linked `-O2` rebuild | Sequential | Overlap |
| --- | ---: | ---: |
| Change cutoff 32 to 31 | 30.166 s | 21.279 s |
| Immediate repeat | 4.078 s | 2.923 s |
| Revert cutoff 31 to 32 | 23.963 s | 20.905 s |
| Immediate repeat | 4.077 s | 3.826 s |

The edit and revert took **54.129 s sequentially and 42.184 s with overlap**
(22.1% less time, one sample per cell). Each edit ran 54 compile requests,
skipped 53 code generations and regenerated one of 943 dependency rows.
Every immediate repeat ran zero builder actions. All 1,763 installed files,
the package database, module artifacts, and linked executable and shared
library matched across the two modes. The dynamic API consumer loaded the
new library and returned the same result in both modes. Preparation
profiles recorded 0 s and 5.473 s of overlap, respectively, and recache
started after both operations. Pueue job 7304 peaked at 4,313 MiB.

Set `HADRIAN_GHC_OVERLAP_REGISTRATION=1` to select the concurrent
Stage1 compiler registration rule for development builds.


### Reuse stripped static archive members

A private replay matched all 883 members of the Stage1 GHC archive to
their original build objects by name, size and content. The recovered
order preserved duplicate basenames. GNU ar reproduced the original
build archive byte for byte. Stripping each object and packing the
results reproduced GNU strip's installed archive, including the symbol
index and member headers.

For timing, an ordinary Stage0 compile reproduced all four artifacts
of the linked `GHC.Utils.Misc` cutoff edit. One static member changed.
The stock arm stripped the complete raw archive. The candidate checked
the input and cached member stamps, stripped the changed object and
repacked all 883 members. The initial cache fill and production of the
raw build archive were outside both timed arms.

| Static archive installation | GNU strip | Reuse stripped members |
| --- | ---: | ---: |
| Change cutoff 32 to 31 | 3.087 s | 1.196 s |
| Revert cutoff 31 to 32 | 3.243 s | 1.342 s |
| Edit and revert per round | 6.237 s | 2.584 s |

The two operations together took 58.6% less time at the median over four
rounds. The candidate won seven of eight individual comparisons. The
forward pair ran stock first and the reverse pair ran the candidate first.
All installed archives matched in bytes and mode. Pueue job 7350 peaked
at 1,456 MiB. This replay measured static archive preparation independently
of Hadrian and the rest of the package copy.

The linked trial kept ordinary Cabal and the Stage1 registration
overlap enabled in both arms. Only the candidate intercepted static
archive stripping. The first attempt invalidated all 883 source
stamps when it remounted the build overlay. The repaired cache checks
the source digest on a stamp miss and verifies the cached output's
stamp before reuse.

| Linked `-O2` rebuild | GNU strip | Reuse stripped members |
| --- | ---: | ---: |
| Change cutoff 32 to 31 | 21.831 s | 15.932 s |
| Immediate repeat | 3.174 s | 2.471 s |
| Revert cutoff 31 to 32 | 23.562 s | 19.481 s |
| Immediate repeat | 2.872 s | 3.926 s |

In this single balanced pair the edit and revert took **45.393 s
and 35.413 s**, respectively (22.0% less time). The candidate
stripped only `GHC.Utils.Misc.o` in both edits. The forward edit
checked one source digest and ran the cache wrapper in 0.969 s.
The revert checked all 883 source digests after remount and ran
the wrapper in 1.368 s. The linked savings exceed the isolated
static-archive savings, so the pair includes other timing variation.

Each edit ran 54 compile requests with 53 codegen skips and
regenerated one of 943 dependency rows. The 1,763 installed files,
package database, module artifacts, linked compiler, shared library
and dynamic API consumer matched. All repeats ran zero builders.
Pueue job 7420 used logical CPUs 20–23 and peaked at 4,269 MiB.
The trial used private tool interposition on Hadrian at `be66a11a99`.

### Development build on this host

Run from a configured GHC development worktree. Set `WORKER_RELEASE` to the prepared worker for that worktree's Stage0 compiler. The worker's `ghc.real-ghc` must resolve to that compiler, and its `ghc.libdir` must exist. The following command queues a linked-compiler rebuild in Pueue. The private directory retains parse records when the worker exits.

```sh
install -d -m 700 "$PWD/_build/worker-cpp-cache"
"$HOME/Code/heavy-management/bin/heavy" --mem 8G --time 20m env \
  GHC_WORKER_CPP_CACHE="$PWD/_build/worker-cpp-cache" \
  HADRIAN_SINGLE_CAPABILITY=1 \
  HADRIAN_DEPENDENCY_WORKER="$WORKER_RELEASE/ghc" \
  hadrian/build -j3 --flavour=quick --docs=none --freeze1 stage2:exe:ghc-bin
```

`--freeze1` reuses the existing Stage0 prerequisites for this benchmark. For a final build, use ordinary GHC and leave the development settings unset.

### Shared Stage1 worker on 27 November

The active shared Stage1 worker `fd8d51d` uses GHC 10.1.20261115.1 (executable SHA-256 prefix `aac58b24`). It ran the 956-module dependency command in 0.577 s unchanged and 0.617 s after a one-import edit. The old worker `2a5a1d0` took 0.589 and 0.608 s in the same test. These are medians from six warm samples per worker per case. Ordinary GHC took 23.284 and 23.498 s in one reference run per case. The edit command was 38.1× faster and regenerated one row. All Makefiles, backups and diagnostics matched ordinary GHC.

The release also handles an up-to-date `-c -dynamic-too` command with Hadrian's optional `+RTS -O64M -A64m -RTS` block. Across six warm samples per executable on a single-file fixture, ordinary GHC took 210.1 ms, the previous worker took 209.4 ms, and the new worker took 19.6 ms at the median (10.7× versus ordinary GHC). A required compile delegated once with the original arguments and reproduced all four artifacts byte for byte.

### Shared Stage0 worker 94c0f01

The active worker uses a bounded binary codec for the optional positive
CPP cache. Both workers used GHC 10.1.20261127 (`cafe7121a8e6`) and the
same 943-module dependency command. Two ordinary GHC controls took
10.747 s and 10.546 s (median 10.646 s).

| Dependency scan | Previous worker `7d77754` | Binary cache `94c0f01` |
| --- | ---: | ---: |
| Admit current records into a nearly full history | 6.327 s | 5.787 s |
| Fresh daemon after admission | 4.308 s | 3.964 s |
| Fresh daemon with a normal populated cache | 5.362 s | 4.422 s |

First admission took 8.5% less time than on the previous worker and
45.6% less than on ordinary GHC. It improved all four alternating pairs.
Restarts after admission improved three of four pairs. The two normal
populated-cache pairs had split results. Median daemon CPU on admission
fell from 6.14 s to 5.49 s. Median peak daemon RSS on restarts after
admission fell from 561.7 MiB to 534.9 MiB.

Both workers added all 104 current CPP records to the same history
fixture with 5,195 synthetic keys derived from real header lists.
The previous worker retained 5,097 historical keys and the new worker
retained all 5,195. Both reused 104 positive and 835 empty results at
restart. Dependency files, backups, stdout and diagnostics matched
ordinary GHC, and all 1,068 watched inputs stayed stable. Pueue 7461
peaked at 561 MiB. Job 7460 covered capacity, invalid stores and
concurrent writers. Job 7471 verified that the packaged shim and daemon
had the timed executable hashes and passed release smoke. The v4 store
uses a separate file and starts filling on first use.

### Shared Stage0 worker 7d77754

The packaged worker reuses the decoded positive CPP store when a
fresh read under the writer lock returns identical bytes. It decodes
the latest bytes when another writer has updated the store. On the
exact 943-module dependency command, the first request against a
nearly full store took **5.138 s versus 5.338 s** with `3c6ed41`.
The candidate won three of four alternating pairs. Median daemon
CPU fell from 5.35 s to 5.05 s. Peak daemon RSS was 560.2 MiB and
560.5 MiB, respectively.

Fresh restarts after admission took 3.787 s versus 3.950 s. Normal
populated-cache restarts took 3.838 s versus 4.013 s across two
pairs. Stock GHC `cafe7121a8e6` took 8.424 s and 8.133 s. Both
workers admitted all 104 current records into the same nearly full
fixture and reused them at restart. Dependency files, backups,
stdout and diagnostics matched stock. Release smoke passed.
Pueue job 7418 peaked at 567 MiB. The opt-in store remains v3.

### Shared Stage0 worker 3c6ed41

With a full positive CPP store and a held-out graph, the shared Stage0
worker's fresh-daemon restart took **4.981 s versus 7.871 s** with
`8a03b68` (36.7% less time). Stock GHC `cafe7121a8e6` took 16.024 s
and 13.914 s. The first request against the full store took 7.924 s
versus 7.773 s. Two normal populated-cache pairs gave medians of
5.479 s and 5.575 s, respectively.

The four alternating full-store pairs used the exact 943-module command.
The fixture put real header lists under 5,193 synthetic historical keys
and left 180 bytes free. The new worker retained the 104 current records
and reused all of them at restart. The previous worker reused zero.
Both reused 835 empty certificates and produced the stock dependency
files, backups, stdout and diagnostics. All 1,068 watched inputs stayed
stable. Pueue job 7345 peaked at 563 MiB. Release smoke also covered
compile fallback, diagnostics, capacity and concurrent writes. The
opt-in v3 store starts in a separate file.

### Shared Stage0 worker ad8a24f

The shared Stage0 release targets the retained GHC 10.1.20261127 executable
(`cafe7121a8e6`). The daemon links a static API companion compiled from
`ea16a92be5` with the matching GHC 9.14.1 bootstrap. Independently built
copies matched in all 882 archive and interface digests.

| Exact 943-module scan | Stock GHC | Worker `2baf1e8` | Worker `ad8a24f` |
| --- | ---: | ---: | ---: |
| Fresh process, populated caches | 8.727 s | 5.548 s | 4.067 s |
| Resident worker, one-import edit | 8.461 s | 0.459 s | 0.447 s |

Both worker rows use four alternating pairs. Stock uses two unchanged
controls and one edited control. The new restart took 26.7% less time
than the preceding worker and 53.4% less than stock. Both worker arms
used 835 empty certificates. The new arm also reused 104 CPP records.
The cache requires an existing private directory set with
`GHC_WORKER_POSITIVE_CPP_CACHE`. With the switch unset, two separate
restart controls had a median of 5.125 s.

The Makefile, backup and diagnostics matched stock, and each warm edit
regenerated one row. The exact packaged release passed ordinary
compilation, unchanged checks and one required stock fallback. Pueue job
7261 ran the paired timings and peaked at 1,101 MiB. Preparation and
activation checks passed
without replacing the ordinary Stage0 executable.

### Shared Stage0 worker 2baf1e8

The Stage0 selector uses worker `2baf1e8` with the same installed GHC 10.1.20261127 executable (`cafe7121a8e6`). On the actual 943-module dependency command, stock GHC took 7.648 s at the median of the two source states. With populated disk caches and fresh daemons, the previous worker `df96e32` took 8.322 s and the new worker took **4.865 s** across four alternating pairs. Both resumed all 835 certificates. The new restart is 36.4% shorter than stock and 41.5% shorter than the previous worker.

The warm one-import edit took 0.465 s at the median across eight requests, **16.5× faster than stock**, versus 0.472 s with the previous worker. Each edit regenerated one row. Stock Makefiles, backups and diagnostics matched across the panel. The installed worker also passed the tuned compile-check and stock-fallback tests. The warmed single-file check took 6.17 ms versus 21.49 ms for stock across six alternating pairs.

### Earlier Stage0 worker df96e32

The earlier shared Stage0 release used `df96e32` and a complete GHC 10.1.20261127 toolchain on a durable path (executable SHA-256 prefix `cafe7121a8e6`). The ordinary 943-module dependency command took 9.527 and 10.041 s in the two reference source states. The warm worker took 0.436 s unchanged and 0.476 s after a one-import edit (20.6× versus the stock reference median). Both worker medians use six samples. Each edit regenerated one row. Makefiles, backups and diagnostics matched. A warm tuned `-c -dynamic-too` check on a single-file fixture took 6.1 ms with the worker and 21.6 ms with ordinary GHC across six alternating pairs. A required compile delegated once with the original arguments and reproduced all four outputs.

The previous shared Stage0 worker pointed to a different installation with a missing Stage0 library directory. Hadrian enables the worker only when it targets the exact compiler path selected for that stage. The linked results above used the same GHC binary bytes in a separate installation.

### Remaining compile requests

The normalized linked edit issued 53 up-to-date compile requests. Forty-eight used CPP and five were boot modules. A private default-CPP check replayed the 48 commands in four paired batches of three clients. The median fell from 3.30 s with ordinary GHC to 2.03 s with the worker. Diagnostics matched. One request delegated in one timed batch. The prototype ran default CPP again through ordinary GHC on an edit that required compilation, so we kept it private.

The existing full-codegen worker ran CPP once per command while replaying the same producer with Hadrian's `-O2 -dynamic-too -fobject-determinism` flags. The original source, an edit, and its reversal each matched all four ordinary GHC artifacts. A separate header fixture matched the warning, the `#line` location of a type error, and the last successful artifacts after that error. The replay redirected outputs to scratch and enabled phase timing. It verifies these two workloads. Hadrian's published build continues to use the check-only worker.

A four-module follow-up compared one ordinary compile per module with two resident compiles in opposite orders. `GHC.Data.FastString`, `GHC.Core.Opt.OccurAnal` and `GHC.Cmm.Pipeline` used their captured `-fobject-determinism` flag and matched all 24 static and dynamic object and interface comparisons. The driver control, `GHC.Driver.Session.Lint`, omitted the flag. Its interfaces matched, and both object variants differed among the three runs. The single ordinary sample leaves the source of that variance unresolved. All eight resident requests matched normal diagnostics, ran CPP once and made zero stock compiler calls.

The wider 45-command compiler-library cohort retained its exact captured flags and outputs on a read-only tree. With three clients, the existing full-codegen worker reduced the median up-to-date batch from 2.735 s to 2.311 s across four alternating pairs. All diagnostics matched and all 180 artifact hashes stayed unchanged. A separate trace showed one CPP invocation per request and zero stock fallbacks.

A private driver built against the same Stage0 GHC API captured the native CPP result, then continued through a fresh GHC process with the original arguments and source. Across the producer edit and revert and four header controls, the native tool ran once per request. The artifacts, CPP warnings, mapped type error and CPP failure matched ordinary GHC. Each successful capture had its own temporary buffer. This establishes the phase boundary. The trial did not measure a speedup or connect the handoff to the resident worker.

A separate stock replay inserted a header earlier in the CPP include path. The source hash and the old recorded header were unchanged. Fresh GHC selected the new header, discovered a different import and rebuilt. A compiler check that reuses preprocessing must also account for changes in header lookup. In a second control, the newly shadowing header changed a macro value and preserved the imports. Ordinary GHC ran CPP, then reported the old object up to date. A forced ordinary compile detected the resulting type error.

The follow-up connected that phase to a private check-only worker. On the same Stage0 toolchain, stock and worker each ran A/A/B/B/A/A with the captured `GHC.Utils.Misc -O2` command and private output paths. All six exit statuses and diagnostic stream pairs and all 24 static and dynamic object and interface comparisons matched. Each request ran CPP once. One resident daemon served the six worker calls. Fresh GHC resumed the three required compiles, and the daemon completed the three up-to-date checks.

A separate fixture matched a newly shadowed header that changed an import, a mapped type error, and custom CPP selected by the command line or source. The custom tool ran once in stock GHC. Setting `CPATH` also selected ordinary GHC. A CPP warning or error ran CPP twice and preserved the ordinary diagnostic streams and status. The private trial used request-local temporary files under stable inputs. It measured phase execution and parity. The shared development route still uses the published worker.

Two fresh workers also replayed the 943-module dependency scan with the retained Stage0 compiler `e4f7bc8`. All 104 CPP buffers differed in exactly one GNU line marker. Only the temporary package-macro header filename changed across 8.29 MB of buffers per run. Both workers matched ordinary GHC's dependency outputs and diagnostics. The direct parser took 1.10 s across those buffers in the first worker, before import lookup and rendering. The second worker hit its memory cap while the first daemon was still resident. Its timing is excluded. A disk certificate would need to identify GHC's actual generated header before abstracting its filename.

A follow-up traced the exact GCC invocation and the file GHC created for each forced package-macro include. The two fresh workers recorded the matching CPP output paths. All 104 CPP buffers shared a certificate key after abstracting only that verified filename and retaining its byte width. Both workers parsed all 104 without warnings or errors. They matched stock Makefiles, backups and diagnostics. The offline key check rejected lookalike and repeated markers and tokens before the location reset. It took a median 9.27 ms across 20 replays over the 104 buffers. All timed dependency scans still used the regular parser and emitter. The key check establishes reuse coverage, and the effect on restart latency still needs an integrated comparison.

The worker's existing marker-free certificates reported hits, while GHC's Makefile emitter still read the flag from the module summaries and parsed those modules. The candidate clears that flag on the certified copies sent to the emitter. With a deliberately invalid buffer substituted after certification, the old path reached the parser and delegated to stock. The candidate reused all 835 certificates and matched stock output. In four alternating pairs with fresh daemons and the same disk cache on retained Stage0 `e4f7bc8`, the median fell from **11.42 s to 7.08 s (38.0% less time)**. All eight runs matched the stock dependency file, backup and diagnostics. This compares worker restart behavior with an already populated cache.

An additive native API now has a private validation build. The CPP runner returns the generated header path together with the exact output. A two-module Stage0 overlay reused the retained GHC API archive and main objects. Its ordinary 943-module scan matched the original Stage0 Makefile, backup and diagnostic streams. This qualifies the native phase boundary for a worker hook. The worker subsequently captured distinct header paths from the native phase for all 104 CPP modules and none for the other 839. The resident repeat reused all 943 summaries and made no new CPP calls. Both worker scans matched the stock Makefile, backup and diagnostic streams. This test records ownership.

A private build wired the phase hook and the stock parser's ordered CPP dependency results into the disk cache. Both modes reused the same 835 empty certificates on every restart. Four alternating fresh-daemon pairs on the 943-module command gave medians of **5.258 s with the positive cache off and 4.050 s with it on**. The positive cache eliminated all 104 CPP dependency parser calls and improved every pair. Import resolution and fresh preprocessing ran in both modes. All outputs matched stock GHC, and 1,068 watched file snapshots stayed equal. The comparison used retained Stage0 `e4f7bc8` and the same three-module GHC API overlay in both arms.

Separate stock-matched controls checked an edited include, a newly shadowing include, parser warnings, CPP failure, and a corrupt or disabled cache. The successful hit reused the ordered paths. The edited and shadowed inputs reparsed, and the corrupt file was retained while the module reparsed.

Hadrian now keeps the raw dependencies directly when a source begins with a common CPP pragma in its first 4 KiB. The linked replay removed 45 certificate subprocesses. It still ran 54 compile requests, skipped 53 code generations, matched the checked stock artifacts and followed with a zero-action no-op. In four isolated, alternating comparisons, the former 45 certificate subprocesses took 247 ms at the median and the source checks took 3.7 ms. The candidate linked edit took 27.86 s in a later, unpaired run.

The changed `GHC.Utils.Misc` producer took 1.40–1.41 s wall in two replays of its actual command. The simplifier accounted for 0.56 s CPU, code generation for 0.34 s, and both interface writes for 0.24 ms. Four output files matched the archived stock hashes. These are compiler-command timings. The linked build also packs the compiler archive, links the shared library and executable, and registers the package.

### Linked rebuild and no-op profiles

A warm linked `-O2` edit on Stage0 `cafe7121a8e6`, worker `df96e32`, and mold ran 54 compile requests and skipped code generation for 53 of them. Shake traced 51 commands for compiler-library modules over an 8.20 s window. Archive creation took 1.36 s and overlapped the 0.96 s shared-library link. Cabal then spent 5.01 s copying the package and 1.14 s computing its ABI hash. Registration recache took 47 ms. The final driver link took 0.30 s. The linked compiler, objects, interfaces and dynamic consumer passed the ordinary-reference checks.

The immediate no-op ran zero builders. Its Shake profile recorded 5,604 `ArgsHash` oracle evaluations, with 8.49 s of summed rule time out of 8.55 s. These durations can overlap. The no-op trace ended at 3.71 s and the command took 6.53 s with profile output enabled. The oracle recomputes the arguments for each target. A cache must also track argument settings that Hadrian reads outside Shake, including the ordered command-line overrides and `hadrian.settings`.

Hadrian now shares the resolved flavour within each invocation. On the warmed linked target with the same Stage0 worker and mold, four alternating no-op pairs took medians of **4.74 s with ordinary flavour resolution and 4.31 s with the cache** (9.1% less time). The cache won every pair. The median paired saving was 0.56 s. Each run executed zero builders and preserved the five checked artifact hashes. A separate profile kept the same 5,604 argument queries and the same dependency sets while reducing their summed rule time from 8.91 s to 7.51 s. Exact arguments matched for vanilla, dynamic, boot and Haddock contexts. The checks also covered CLI overrides, creation and removal of `hadrian.settings`, and `--directory`.

Caching only the GHC include and package argument fragments gave mixed wall-clock results across three balanced rounds. The combined cache preserved every recorded dependency, including 3,781 generated header dependencies and 3,771 package DB stamp dependencies. This trial stays private.

A separate private Hadrian driver persisted 1,706 Stage1 argument hashes. It retained the ordinary argument-hash oracle and validated the cached result with the running executable, both working directories, CLI and parsed settings, process environment, and the recorded dependencies. Contexts with optional `.buildinfo` files delegated to ordinary resolution. Four alternating no-op pairs on the linked target took medians of **4.38 s with ordinary argument resolution and 3.55 s with persistent hashes** (18.8% less time). Every pair improved. All runs executed zero builders and retained the checked artifact hashes.

The controls matched ordinary hashes after CLI and `hadrian.settings` changes. An executable change and an environment change refilled the cache. A linked producer edit reused the warmed cache and issued 303 compile requests. Only the producer generated code. The checked module artifacts, archive, and runtime consumer matched the ordinary reference. This pilot stays private. It uses the entire process environment as part of its invocation key, so incidental environment changes can erase warm reuse.

A follow-up tracked optional Cabal `.buildinfo` files within the cached context rule. One fixture migrated a populated Shake database and checked precedence, additions, edits, removal, dangling symlinks and Cabal's duplicate-file diagnostic. On the real Stage1 compiler build, the cached `cutils.c` arguments and hashes matched ordinary resolution across every tested change. Changes to the selected file refreshed the probed hash once. Editing a shadowed file and repeating unchanged requests reused the hash. The linked target ran zero builders after overlay preparation, and all five checked artifact hashes stayed equal. This follow-up did not benchmark the wider cache.

Two separate capped Pueue jobs then checked the broader private cache on the linked target. A launcher wrapper removed queue metadata immediately before executing Hadrian. The argument cache still fingerprinted the entire environment received by Hadrian and its children. The first job stored 5,135 hashes, and the second job began with zero refills. Passing the raw launcher environment or changing `CC` refilled all 5,135. Every invocation after the primer ran zero builders and preserved five linked artifact hashes.

The opt-in `HADRIAN_PERSISTENT_ARGS=1` is now available for selected Stage1 rules with the built-in `perf+no_profiled_libs` flavour. The released form keeps duplicate environment keys in order and falls back to ordinary resolution for a shadowing custom flavour. On warmed linked no-ops, four unprofiled alternating pairs took medians of **5.356 s with the option off and 2.897 s with it on**. The option improved all four pairs. Both modes ran zero builders and preserved five checked artifact hashes. The timing job used the same retained Stage0 and worker in both modes and primed each arm before timing.

The tightened release candidate also passed a two-job test. The second job reused 5,135 hashes, while changing `CC` or reversing duplicate environment values refilled them all. Repeating the new duplicate order reused all hashes. Turning the option off removed the outer argument rules' dependency on the persistent cache. The checks used an unchanged source tree and recorded zero builder actions.

### Linked edits with persistent arguments

A second comparison used the published Hadrian binary, shared worker `2baf1e8`, Stage0 `cafe7121a8e6` and mold. Both modes used `perf+no_profiled_libs --freeze1 -j3` with one Hadrian capability and logical CPUs 20–23. An untimed linked run prepared the same invocation arguments after the dependency primer. The forward pair ran with the cache off first, and the revert pair ran with the cache on first.

| Linked `-O2` build | Ordinary arguments | Persistent arguments |
| --- | ---: | ---: |
| Change cutoff 32 to 31 | 21.311 s | 19.246 s |
| Immediate repeat | 5.833 s | 2.422 s |
| Revert cutoff 31 to 32 | 20.037 s | 18.939 s |
| Immediate repeat | 4.378 s | 2.923 s |

The edit and revert took **41.348 s with ordinary resolution and 38.185 s with persistent arguments** (7.6% less time). Each edit ran 54 compiler requests, skipped code generation for 53, and regenerated one of 943 dependency rows. Both modes produced identical executables and shared libraries for each source state. The checked module artifacts and archive matched ordinary GHC, and the dynamic GHC API consumer loaded the newly installed library. Each no-op ran zero builders. Each cell is one sample.

A private Stage0 frontend read the stored ABI fingerprints without loading declarations and instances into the external package state. On Cabal's exact 880-module command, the same executable took a median 0.89 s with direct reads and 1.31 s with the ordinary loader across four alternating pairs. Both modes emitted the same hash as stock GHC. Controls matched for duplicate and reordered modules, an external module, a missing module, dynamic-interface validation and a malformed header. A damaged lazy interface section can require validation beyond the fields read by this experiment. The comparison used the capped GHC queue and shared the host.

A private Hadrian candidate ran package copy and ABI calculation in parallel for the Stage1 compiler library. Shake recorded the entire 1.29 s ABI calculation inside the 5.14 s copy. The registration window fell from 6.20 s to 5.20 s in one forward edit per mode. The full profiled commands took 24.22 s and 21.74 s. Other build phases also varied between runs. Both modes ran the same 54 compile requests, regenerated one dependency row, and matched the checked artifacts and runtime consumer. Both immediate repeats ran zero builders. The experiment used the published worker and kept the two operations private.

### Development workers at 8ad5a4d

Both stages use `8ad5a4d`. A warm edit of one import in a 956-module graph took **0.582 s versus 10.438 s stock at Stage0 (17.9×)** and **0.619 s versus 23.379 s stock at Stage1 (37.8×)**. The worker reused rendered dependency rows when their paths matched. The release also fixed stale single-file compilation results after package and environment changes. [Raw scan samples](release-8ad5a4d.json)

| 956-module scan | Stage0 stock | Stage0 worker | Stage1 stock | Stage1 worker |
| --- | ---: | ---: | ---: | ---: |
| Warm repeat | 10.232 s | 0.566 s | — | 0.597 s |
| Empty disk cache, first scan | 11.845 s | 10.638 s | — | 23.174 s |
| Restart with populated disk cache | 11.845 s | 6.586 s | 23.586 s | 10.929 s |

Warm Stage0 timings are medians from three balanced comparisons. The prior worker took 0.648 s on a warm repeat and 0.583 s on the edit. Stage0 median sampled peak RSS was approximately 576 MiB for the candidate and 294 MiB for stock. Stage0 cold fill and restart each used one sample per worker, between two stock controls. Stage1 restart and edit used two order-balanced pairs. Restarts reused all 848 eligible records at both stages. Makefiles, backups and diagnostics matched stock.

A linked compiler edit in `GHC.Cmm.Pipeline` took 41.26 s with stock defaults, 19.64 s with one Hadrian capability, and 11.67 s when a warm worker also handled the dependency scan. Those three-run medians used an earlier release. A separate experiment gave each library stamp one writer and measured BFD and mold at 12.12 and 9.33 s on the same edit. [Linked-target comparison](#linked-rebuild-with-the-hadrian-runtime-option) · [Library stamp and linker experiments](rebuild-c33551f.md)

A `GHC.Utils.Misc` edit triggered 305 compiler invocations. In a private trial the worker completed 253 of GHC's recompilation checks and delegated the remaining requests to ordinary GHC. The median linked rebuild took 31.70 s versus 34.90 s with ordinary compilation throughout. The compiler, libraries and measured module artifacts matched byte for byte in both source states. [High-fanout timings and artifact checks](high-fanout.md)

### Development workers at fa68e89

A previous diagnostic-free parse can establish that a module has no CPP prerequisites or source line markers. The worker saves this result in a bounded file. After a restart it checks the preprocessed source and parser settings, then asks GHC to resolve imports and emit dependencies. Linux workers verify the executable and file-backed executable mappings before using the file. Replacing a library at the same path invalidated earlier records in the verification fixture.

| GHC 10 dependency command | Stock | Restart with disk cache | In-memory repeat |
| --- | ---: | ---: | ---: |
| Stage0 compiler, 956-module scan, three pairs | 10.88 s | 7.77 s | 0.594 s |
| Stage1 compiler, 956-module scan, two pairs | 26.81 s | 14.99 s | 0.685 s |

The first Stage0 scan to populate the cache took 12.06 s. A fresh Stage0 worker with the disk cache disabled took 10.83 s in one control. On the first edit after restarting it reused 827 of 828 eligible parses. Stage1 took 27.42 s to populate its cache. The Stage1 hot edit took 0.689 s versus 26.42 s stock. All reported dependency files, backups, diagnostics and statuses matched stock. Stage1 used the captured dependency command with that compiler and its libdir.

The two stages need different worker builds on this host. The Stage0 executable links the GHC 10 library built by the bootstrap compiler. Building the daemon with that Stage0 executable normally loads the shared GHC library built for Stage1. The new Stage0 worker links the same GHC 10 API archive as its stock compiler. In the initial comparison, a prefilled restart took 7.92 s with the archive-matched worker and 14.22 s with the dynamic worker. The GHC library and RTS both changed. The Stage1 worker continues to use the shared library.

The full linked-target edit took 45.07 s with default settings in one control. With one Hadrian capability, two order-balanced runs took a median 22.20 s with stock scans and 12.07 s with the new Stage0 worker. These two arms used the same Hadrian configuration. The worker saved 9.61 s and 10.64 s respectively. All 17 artifacts and the optimized consumer matched stock. The worker's disk option was unset during these builds. The savings came from the resident worker. Priming times are reported separately because changing the selected scanner causes additional package rules to run.

On a separate `GHC.Cmm.Pipeline -O2 -c` benchmark, median wall time across three post-warmup rounds was 0.468 s stock, 0.230 s on the static Stage0 worker and 1.141 s on the previous dynamic worker. Median sampled peak RSS was 170, 460 and 551 MiB respectively. Twelve additional one-shot fixtures covered instances, boot imports, rewrite rules and an expected failure. Outputs and diagnostics matched. The scoped Hadrian Stage1 `GHC.Cmm.Pipeline.o` edit took 11.10 s stock and 2.17 s with the worker handling both `-M` and `-c`, a 5.12× speedup across three alternating pairs. All five output files matched, including dynamic objects and interfaces. This was a separate worker-routing experiment. The normal `HADRIAN_DEPENDENCY_WORKER` setting selects only dependency scans. [Release evidence](release-fa68e89.json)

### Linked rebuild with the Hadrian runtime option

We ran the same `GHC.Cmm.Pipeline` edit and linked-compiler target in three rounds. Each configuration occupied the first, second and third position once. All used the same Hadrian executable and stock Shake 0.19.9. Setting `HADRIAN_SINGLE_CAPABILITY=1` changes the RTS running Hadrian. Shake still has three external job slots. The compiler and worker use their own RTS settings.

| Configuration | Median edit to linked compiler | Median no-op |
| --- | ---: | ---: |
| Stock GHC, default Hadrian | 41.26 s | 25.20 s |
| Stock GHC, one Hadrian capability | 19.64 s | 4.78 s |
| Worker for scans, one Hadrian capability | 11.67 s | 4.84 s |

Together the changes gave **3.54×** on the edited build. The Hadrian option alone gave **2.10×** on the edit and **5.27×** on the no-op. Each of the nine edits ran one dependency scan, three ordinary module compilations, one archive action, two link actions and one package recache. All nine no-ops ran zero builder actions. The worker regenerated one of 956 rows on each edit it handled. All modes produced the same 17 artifacts, including both dependency files, both GHC libraries and the linked compiler. The optimized consumer also matched stock and returned 156.

We primed each arm with the original source before timing the edit. Across three rounds the primes took a median 40.33 s stock, 19.79 s with the Hadrian setting alone, and 50.38 s with both changes. Switching scanners caused extra package dependency rules to run in some priming builds. Those builds ran 43 actions, including 36 scans. The others ran eight actions, including one scan. During the first combined prime, three external GHC commands overlapped. Archive and link commands overlapped during its measured edit.

The main comparison used four logical CPUs on two physical cores on WSL2. On no-ops, median system CPU dropped from 13.27 s to 0.57 s with the Hadrian option. A diagnostic build that set the capability count directly in Shake reduced median no-op wall time from 26.34 s to 5.00 s across three pairs. Median GC CPU rose from 0.74 s to 1.33 s. This points to time spent outside GC. With stock Shake and one logical CPU from each of four distinct physical cores, three further no-op pairs took **25.21 s** with default settings and **4.90 s** with one capability (5.15×). Both CPU layouts were on the same machine. [Timings, action counts and topology](hadrian-capabilities.json) · [Hadrian option](../../hadrian/src/Main.hs)

### Thread migration during Hadrian dependency checks

The `-qm` RTS flag disables automatic thread migration. It can be passed directly to the standard Hadrian wrapper. A wrapper smoke used the machine-readable RTS report to verify that Hadrian received the flag.

```sh
hadrian/build -j3 --flavour=quick --docs=none --freeze1 stage2:exe:ghc-bin +RTS -qm -RTS
```

We measured the real `GHC.Cmm.Pipeline` edit in forward and reverse order on the same two physical cores. Hadrian retained all three RTS capabilities and its three external job slots with `-qm`. Stock took a median 39.09 s to link the compiler, 24.89 s with `-qm` alone and 13.95 s with `-qm` and worker `55f502b`. Corresponding no-ops took 26.76, 6.15 and 5.57 s. All six edits ran eight actions and all no-ops ran zero. The 17 artifacts matched and the optimized consumer returned 156.

A separate no-op run used four distinct physical cores. Disabling migration brought median condition waits from 710,420 to about 9,444 and wall time from 26.09 to 5.03 s. A native probe of the default reported 1,370 of 1,380 sampled signals along the path from `stg_putMVarzh` through `sendMessage` to `giveCapabilityToTask`. All 1,376 sampled waits came from `yieldCapability` in scheduler workers. This connects cross-capability wakeups to the slowdown on this workload. Hadrian used the GHC 9.14.1 bootstrap RTS. The comparison used the same GHC 10 targets throughout. [Timing samples, pthread counts and stacks](thread-migration.json) · [Measured RTS scheduler](https://github.com/ghc/ghc/blob/902339d332fb4ce2b3c87dcac1ee6495d41ad886/rts/Schedule.c)

### Research priorities

1. **Extend restart reuse to more modules.** Of the 108 modules that still required parsing, 104 produced preprocessed buffers with different temporary paths after restart. Their parses and the four other parses cost about 1.3 s combined. Measure validation overhead before extending cache eligibility. [Cold dependency scans](#cold-dependency-scans-after-worker-restart)
2. **Validate reuse inside an optimized Core binding.** Recording transitive rule heads detected a change behind an inlined wrapper. Four local lookups from the first visit to `doesDirNameExist` could not be validated at binding entry. Account for those local dependencies, substitution and floated bindings. Compare every proposed reuse with a fresh optimization. [Core measurements](#where-optimization-time-survives-a-small-edit)
3. **Measure thread migration on other builds.** The no-op traced most condition signals to cross-capability MVar wakeups. Repeat on another machine and at a wider job count before considering a default. The compiler worker and the GHC executable have different allocation and parallelism profiles. [Compiler RTS measurements](#rts-cost-during-compilation)

### Hadrian dependency caching

Set `HADRIAN_DEPENDENCY_WORKER` to the absolute path of a prepared worker's `ghc` executable for development builds. The retained stage0 compiler on this host uses the following setting.

```sh
export HADRIAN_DEPENDENCY_WORKER="$WORKER_RELEASE/ghc"
```

Run the usual Hadrian target through Pueue. Hadrian selects the worker for Haskell dependency scans when its recorded compiler path and executable hash match the stage compiler. Other stages use their own compiler. Leave the variable unset for final builds. The digest covers the executable. Prepare a new worker after separately replacing shared libraries.

Worker `21fb2cf` recognizes Hadrian's `+RTS -O64M -RTS` option and starts a separate daemon with that setting. Its predecessor forwarded this command to stock. Using the exact stage0 compiler for the Stage1 compiler package, a comment edit took 14.52 s stock and 2.75 s warm for the `.dependencies.mk` rule. It regenerated one of 956 modules and emitted byte-identical output (5,244,968 bytes).

For the `--flavour=quick` (`-O0`) `GHC.Cmm.Pipeline.o` target, the same type of edit took 14.74 s stock and 2.97 s warm (4.96×). Each arm ran one `-M` and one `-c`. The worker handled the scan, and the ordinary compiler rebuilt the object. The edited interface changed from the primed one. The Makefile, static and dynamic objects, and both interfaces matched between arms. No-op times were 2.23 s and 1.69 s, with zero compiler invocations.

For an optimized rebuild we changed a string on the right-hand side of `cpsTop`, from `Post CPS Cmm` to `Post CPS Cmm pass`. Hadrian appended `stage1.ghc.ghc.hs.opts+=-O2` to the quick flavour. The last optimization flag in each compilation command was `-O2`. For each arm we restored the same pre-edit Shake database and optimized objects. With release `21fb2cf`, across five pairs, stock took a median **16.38 s** and the worker **3.06 s**, a 5.35× ratio of medians (4.97× median paired speedup). No-ops took 1.83 s stock and 1.79 s with the worker. The edited object differed from the primed one. The Makefile, both objects and both interfaces matched stock in all five pairs. Each edit used one dependency scan and one ordinary GHC compilation. The benefit here came from dependency discovery. [Individual edit pairs and hashes](pipeline-o2.json)

The dependency-only and `-O0` measurements above are single pairs on a shared host. All three experiments retained prerequisites outside the target. A complete self-build also runs other package rules and linking.

### Whole compiler target

Hadrian built `stage2:exe:ghc-bin` with `--flavour=quick --freeze1 -j3` in a private copy of GHC 10. It ran the ordinary Stage1 prerequisite and link rules. The stock warm-up after relocating the tree took 405.51 s. We then added `&& splitting_proc_points` to the `cmmOptElimCommonBlks cfg` guard in `GHC.Cmm.Pipeline`. Each measured edit rebuilt the module and two direct importers, the static and dynamic GHC libraries, and the linked compiler.

| Edit with worker 21fb2cf or its stock compiler | Wall time | Dependency scan |
| --- | ---: | --- |
| Stock | 48.70 s | Ordinary GHC |
| Worker after scanning several packages | 59.61 s | Full, 956 modules |
| Worker with the compiler graph resident | 32.97 s | Partial, 1/956 |

These are single observations. The warm scan reduced end-to-end time by 32.3%. The first worker edit took 22.4% longer than stock. Another package scan can evict the compiler graph from this release's two entries. The full-target trace shows the miss. It does not record the precise eviction or argument change that caused it. Both worker builds matched the stock compiler executable, measured module artifacts and dependency file byte for byte. The resulting compilers built the same optimized test executable, which returned 156.

The no-op took 31.74 s stock and 26.26 s with the warm worker. Neither ran a builder action. A separate Shake timing run at `-j3` put 30.44 of 31.82 s in rule evaluation. The process allocated 11.63 GB and spent 1.24 CPU seconds in GC. One `-j1` no-op completed in 6.12 s. Shake 0.19.9 also changes the number of RTS capabilities with the job count. That experiment varies both at once.

Release `55f502b` retains the two recent scans and can retain one older graph larger than those two combined. This keeps the compiler graph after small package scans. It also tracks the appearance and disappearance of files named by raw, Haskell or CPP-generated source line markers.

We repeated the full-target edit using the revised release. Stock took **42.46 s** and the worker **32.28 s** (1.32×, 24.0% less elapsed time). The worker regenerated 1 of 956 modules on the first measured edit after its cold package scans. Stock and worker no-ops took 26.66 and 25.90 s. Both ran zero builder actions. The priming builds took 46.70 s stock and 62.88 s worker. The scope was the linked GHC executable and its normal Stage1 prerequisites. There was one edit pair, so the timings include host variation.

The linked compiler, both GHC libraries and the static and dynamic object and interface files for all three modules matched stock. The compiler built an optimized consumer whose interface, object and executable also matched. The consumer returned 156. [Whole-target timings and hashes](whole-55f502b.json)

With the same release, we repeated the optimized `GHC.Cmm.Pipeline.o` target experiment. The five alternating pairs took a median **11.86 s stock and 2.49 s warm** (4.76× by medians, 4.86× median paired). Every edit ran one dependency scan and one stock compilation. All five output files matched in all ten runs. The corresponding no-ops took 1.46 s and 1.39 s and ran no compiler. Stock times also changed between releases. Use the matched stock result for each comparison. [Optimized object measurements](pipeline-o2-55f502b.json)

The separate Stage1 worker served the same 956-module compiler dependency graph in a direct command benchmark. After two intervening small scans, one import edit took 26.912 s stock and 0.713 s warm (three-pair medians, 37.7×). The cold times were 27.088 s stock and 26.293 s worker. The warm daemon reached 749 MiB sampled RSS. Both promoted paths also passed response-file, tuned RTS and line-marker checks. Creating or removing a line-marker target refreshed one of three modules. An unchanged repeat reused all three. The Makefile, backup and diagnostics matched stock.

### Cold dependency scans after worker restart

We profiled the Stage1 compiler package's 956-module `-M -include-cpp-deps` command with its stock Stage0 GHC. Dependency discovery allocated 2.64 GB and took 1.40 CPU seconds. The 956 parser calls allocated 15.24 GB and took 9.18 CPU seconds in total. Building the Makefile requires GHC to collect the extra source files that CPP and source line markers name. The uninstrumented process allocated 24.06 GB and took 15.95 CPU seconds. These are compiler-process measurements. Clang implements a separate scanner for directives that affect include dependencies. GHC also reports parse errors through this path. Reusing a previous successful parse requires preserving those diagnostics after an edit. [Clang directive scanner](https://github.com/llvm/llvm-project/blob/main/clang/include/clang/Lex/DependencyDirectivesScanner.h) · [Dependency emitter](../../compiler/GHC/Driver/MakeFile.hs) · [Cold-scan phase totals](cold-scan.json)

Two fresh Stage0 processes produced identical preprocessed-input fingerprints for **852 of 956 modules** with unchanged source. After adding `import GHC.Data.Bool ()` to `GHC.Cmm.Pipeline`, 851 matched. Dependency discovery took 3.52–3.53 s per process. Hashing all 32.6 MB took 37–39 ms. All 104 unchanged-source misses involved CPP output. We compared two 81,552-byte `GHC.hs` buffers directly. Only three PID digits in the filename of a generated header in a CPP line marker differed. The other 103 require separate investigation. This measures the cost and stability of one input to the cache key. Import resolution, diagnostics and output parity also need validation. [Fresh-process measurements](preprocessed-fingerprints.json)

An extension under consideration is to store complete per-module dependency rows. Release `fa68e89` stores the successful empty CPP parse result. Start a new daemon, run GHC's dependency discovery and check the discovered edges before reading saved rows. Key the cache on the worker format, exact compiler and libdir, package environment, working directory and arguments. Fingerprint the actual preprocessed Haskell input (`ms_hspp_buf` or `ms_hspp_file`). GHC's `ms_hs_hash` identifies the source before preprocessing. Resolve each import with the fresh Finder, including the selected external interface path. Two installed package layouts can select different prerequisites for the same module name. Check the existence of all recorded line-marker targets, including paths that did not exist. Restart with empty GHC session state. Regenerate rows that produced diagnostics. Initially record which rows the disk cache would have returned and continue to run the ordinary emitter so every predicted hit has a stock comparison. Verify the resulting bytes and diagnostics against stock after restarting the daemon and after changing each input. Include a generated module that begins to shadow an existing import. [Source hashing in the downsweep](../../compiler/GHC/Driver/Downsweep.hs)

### Reuse inside an edited module

GHC 10 checks the source fingerprint when deciding whether to recompile a module. For an importer it can also check fingerprints of individual declarations it used. This already avoids downstream work. We measured what remains identical inside a module selected for recompilation. [Recompilation checker](../../compiler/GHC/Iface/Recomp.hs)

We changed one condition in the private function `cpsTop` in `GHC.Cmm.Pipeline`. The edit required `splitting_proc_points` for common-block elimination. We compiled both sources at the same path using the same dependencies and `-O2 -fforce-recomp -split-sections`. The compiler was GHC 10.1.20261115.1, source revision `945ea7a737`, on x86-64 WSL2.

With `-fobject-determinism`, 52 of 57 named text sections retained their bytes and GNU relocation records. They held 5,709 of 12,024 original text bytes (47.5%). One section retained its bytes but changed relocations. With default naming, zero sections matched all three criteria. Two stock builds of the original matched in full. With deterministic naming, worker `39af263` matched stock on both versions. [Deterministic Cmm names](../../compiler/GHC/Cmm/UniqueRenamer.hs)

Before Cmm optimization, 55 of 56 nonempty groups had identical printed contents. They held 31,765 of 121,347 printed bytes (26.2%). We removed only dump headings, timestamps and surrounding line breaks. Repeated stock builds of the original and warm worker builds of both sources reproduced the corresponding dumps, objects and interfaces.

The stock compiler's eventlog identified 59 timed Cmm pipeline calls. Three received empty groups. In two runs of each source, the 55 matching nonempty groups allocated exactly 7,638,912 bytes. This was 21.3% of the original Cmm pipeline allocation and 3.6% of total code-generation allocation. Their measured spans summed to 4.1–5.4 ms on the original. The single changed group took 78.5% of Cmm pipeline allocation. These timings cap the gross opportunity for skipping these calls on this edit. Cache lookup and validation still take time.

A candidate reuse boundary is `cpsTop`, before the module-wide static reference table pass. Its result includes CAF information and an updated unique supply. A cache must validate or reproduce both, as well as platform settings and optimization flags. Rust's query system tracks dependencies and compares result fingerprints across builds. GHC already supports writing simplified Core to disk with `-fwrite-if-simplified-core`. It stores the result after optimization. To target repeated optimizer work, measure stable groups and phase costs before and during simplification. Validate cross-binding inlining, specialization and rule dependencies against a stock build. [Interface construction](../../compiler/GHC/Iface/Make.hs) · [Cmm pipeline](../../compiler/GHC/Cmm/Pipeline.hs) · [Rust incremental compilation](https://rustc-dev-guide.rust-lang.org/queries/incremental-compilation-in-detail.html)

### Where optimization time survives a small edit

In `GHC.Utils.Misc` we changed the edit-distance helper's `Word32` cutoff from 32 to 31. We compiled both versions with stock GHC 10 at `-O2`. Two repeats of the original gave identical desugared and final Core dumps after removing dump headers and timestamps. We compared complete top-level groups as multisets, retaining printed uniques, types, coercions, binder metadata, recursive groups and right-hand sides.

Of 153 desugared groups, 152 matched after the edit. Of 309 final groups, 308 matched. The only textual difference in each unmatched group was the changed literal. The 1,142 rule-firing records and the printed local rules also matched. Repeated object and interface files agreed within each source version.

The ten simplifier invocations took 3.39–3.69 CPU seconds and allocated 5.405 GB per baseline run. The first invocation alone took 566 ms and allocated 986 MB in the first run. Those are whole-pass costs. To establish the value of a cache, attribute the cost to candidate groups, then record which unfoldings, rewrite rules and other binder information the simplifier actually reads. An unchanged result can depend on a changed optimization input. LLVM ThinLTO includes imported functions and global analysis decisions in its incremental cache key. GHC would need a corresponding account of its own dependencies. [Simplifier iteration](../../compiler/GHC/Core/Opt/Simplify/Iteration.hs) · [ThinLTO design](https://blog.llvm.org/2016/06/thinlto-scalable-and-incremental-lto.html)

We then instrumented the first simplifier invocation in a separate Stage0 GHC 10 compiler. The stock and uninstrumented relink had identical pass allocation (180.97 MB). The probe added 4.1% allocation. Across four iterations it attributed 158.27 MB to binding groups. Groups with no observed Core change accounted for 150.25 MB (94.9% of attributed allocation). The edited helper itself accounted for 1,024 bytes in iteration one, but the literal also reached `fuzzyLookup`, which accounted for 4.67 MB. The largest unchanged group in that iteration, `doesDirNameExist`, accounted for 15.52 MB. These measurements apply to the Stage0 compiler. The Stage1 timings above use a different build of GHC.

Start by recording successful and failed unfolding and rewrite-rule lookups for one expensive, unchanged nonrecursive binding. Compare the complete result with ordinary simplification on every run. Track floated bindings, substitution, scope, fresh names and simplifier ticks before attempting to skip work. Identical printed output across one edit alone cannot establish cache validity.

### Which simplifier inputs determine an optimized binding?

A private GHC 10 Stage0 compiler traced rule lookups and inlining attempts while simplifying `GHC.Utils.Misc.doesDirNameExist` at `-O2`. Its 794 recorded decisions matched in order across two original runs and an unrelated edit to the edit-distance cutoff. The trace contained 397 empty rule lookups, 395 rejected inline attempts and two accepted attempts. It covered 71 visits to a binding with that name over the optimization pipeline. Objects and interfaces from the instrumented compiler matched stock for every tested version.

A controlled edit shows why replaying just those decisions can produce stale code. We gave the binding an `INLINE` helper and changed that helper from `take 13` to `take 14`. The caller's source stayed the same. All **982 recorded decisions** in the caller matched, but its optimized worker called `$wunsafeTake` with `13#` in one build and `14#` in the other. This immediate was the only difference in the final Core dump after removing the header.

Adding a fingerprint for each expression selected for inlining detected the changed helper. Of six accepted inlining attempts, exactly the helper's fingerprint differed. These diagnostic fingerprints use GHC's printed Core. A reusable cache key still requires a stable encoding, the other inputs to each transformation, and validation against stock results. This experiment measured dependencies and did not skip optimization work. [Probe results and output hashes](simplifier-inputs.json) · [Simplifier](../../compiler/GHC/Core/Opt/Simplify/Iteration.hs)

The next shadow probe recorded only whether each resolved identifier
had an empty list of visible rules. Across the original source,
repeat, cutoff edit and revert in `GHC.Utils.Misc`, the precheck
allocated 4.38–4.41 MB and took 7.82–11.63 ms. It resolved all eight
external first-visit identifiers. Resolving those identifiers and
reading the rule environment accounted for 97.6–98.2% of the
allocation. Four local lookups still prevent binding reuse. The
diagnostic compiler and stock GHC produced identical objects,
interfaces and diagnostics for all four runs.

The orphan-rule fixture produced 6, 6 and 46 in both compilers.
Adding the unrelated rule preserved the certificate. Adding the
relevant rule changed exactly the target's empty-list result.
Built-in heads had visible rules in all three cases, so the
empty-only check declined reuse. The probe ran ordinary simplification
throughout. Pueue job 7402 used the GHC 10.1.20261115.1 compiler
relinked from revision `945ea7a737`.

The demand-driven shadow resolver collected only requested names and
stopped once it found them. It reduced resolver allocation from
4.30 MB to 3.92 MB across four matched `GHC.Utils.Misc` requests.
That still left about 4.0 MB of total validation allocation and four
unresolved local lookups. The old and new resolvers produced the same
tested certificates and verdicts. Both matched stock diagnostics and
artifacts. The orphan-rule fixture again returned 6, 6 and 46 and
matched stock. Timings varied. Early stopping still needs a guarantee
that one stable name identifies the same `IdInfo` after substitution
before it can support binding reuse. Pueue job 7445 used the same
GHC 10.1.20261115.1 relink setup.

### Cmm assignment sinking

Research commit `96cbe8010a` skips conflict checks for a live destination with a nontrivial right-hand side. All outcomes of those checks retain the assignment. The candidate stays on the research branch.

| Forced module at `-O2` | Baseline wall | Candidate wall | Baseline allocation | Candidate allocation |
| --- | ---: | ---: | ---: | ---: |
| Generated 200-field applicative | 0.7140 s | 0.6654 s | 1,704 MB | 1,519 MB |
| GHC.Cmm.Sink | 0.6023 s | 0.6167 s | 530.4 MB | 530.0 MB |
| GHC.Utils.Misc | 1.9518 s | 1.7728 s | 1,997.5 MB | 1,995.7 MB |
| GHC.Data.Bool | 0.2133 s | 0.2254 s | 163.6 MB | 163.6 MB |

The table gives medians from five interleaved runs after one warm-up. We relinked both GHC 10 executables from the same retained package and main objects, changing only `GHC.Cmm.Sink`. This package used the GHC 9.14.1 bootstrap RTS. The sinking source matched the research base `56bb91d95f`. All measured pairs had identical object and interface files. A separate GHC API driver at the research base used 6.107 GB and 1.633 CPU seconds on the 400-field case, down from 7.749 GB and 1.905 seconds. The GHC modules give mixed elapsed times.

We ran a 200-field consumer with stateful IO actions against each producer. The worker compiled the consumer and stock GHC linked both executables. The executables had identical SHA-256 hashes. With seeds 7 and 41, both returned the expected sums, position-weighted sums and counters.

A separate shortcut in Core simplifier rule lookup reduced total compiler allocation by 0.31% on `GHC.Utils.Misc` and 0.27% on `GHC.Data.FastString`. Median CPU times stayed within 1 ms of the controls. We discarded that candidate.

A separate Stage1 experiment compiled only `GHC.Core.Opt.Simplify.Iteration` with `-O2` inside the otherwise quick compiler. Against matched static relinks using the original Stage1 interfaces, the median paired workload savings across four runs were 195 ms for `GHC.Utils.Misc` and 36 ms for `GHC.Data.Bool`. The objects and interfaces matched dynamic stock GHC. Simplifier allocation fell by about 0.7% in both cases. Rebuilding `Iteration` itself took an additional 1.14 s and 53 MiB peak RSS. We kept this as a local experiment because each workload included one nearly flat timing pair.

### RTS cost during compilation

We ran the retained GHC 10.1.20261115.1 compiler with its own threaded dynamic RTS. Four concurrent processes used four physical cores in one Pueue job with a 2 GiB memory cap and swap disabled. Each process compiled a separate copy of its target. GC CPU is summed across the four processes. Peak memory is sampled for their cgroup.

| Four-process workload | Rounds per setting | Median wall, default / 64 MiB nursery | GC CPU, default / 64 MiB | Peak memory, default / 64 MiB |
| --- | ---: | ---: | ---: | ---: |
| Two GHC.Cmm.Sink and two GHC.Data.Bool | 6 | 2.161 / 2.049 s | 1.521 / 1.044 s | 254 / 470 MiB |
| Four GHC.Cmm.Sink | 4 | 2.299 / 2.162 s | 2.148 / 1.586 s | 427 / 636 MiB |

The 64 MiB nursery cut median wall time by 5–6%. Timing ranges overlapped. All objects and interfaces matched. The extra 209–216 MiB matters when several builds share a machine. We kept the existing defaults. The [individual samples](2026-11-27.csv) include smaller nursery settings.

On the actual Stage1 `-O2 -dynamic-too` command for `GHC.Core.Opt.Simplify.Iteration`, the 64 MiB nursery saved 0.75 s of CPU at the median across three paired rounds. Median process peak RSS rose from 349 MiB to 369 MiB. All four emitted artifacts matched across the runs. Other builds were active, so these samples measure per-command CPU and RSS. The nursery has its own development opt-in. [Hadrian setup](../../hadrian/README.md#compiler-nursery-for-development-builds)

Across four paired samples per module, the same nursery setting saved a median 0.10 s CPU when emitting `GHC.Utils.Misc` and took a median 0.015 s more CPU when emitting `GHC.Tc.Gen.Expr`. Peak process RSS rose from 195 to 221 MiB and from 428 to 431 MiB, respectively. All four output files for each command matched ordinary GHC. This panel measured individual compiler processes.

In a separate Callgrind run, sequential evacuation in `evacuate1` used 474,394,570 of 3,386,978,025 instructions (14.0%) in the compiler process building `GHC.Data.Bool`. Both artifacts matched the uninstrumented build. Of 8,694,351 pointer classifications, 4,618,238 took the static path. Of 2,540,069 ordinary closure dispatches across 16 targets, the largest target received 743,727. Removing the suspected extra flag load would save at most 0.12% of the routine's instructions. This profile gives little support for specializing one closure type. The `GHC.Cmm.Sink` profile reached its 100 s limit without usable instruction counts. [Evacuation code](../../rts/sm/Evac.c)


### Capability count in the worker daemon

A separate test sent four simultaneous compilation requests to one warmed `21fb2cf` Stage0 worker on four physical cores. Each request compiled a different GHC module. With the daemon's default `-N`, the median wall time to finish all four was 9.00 s. Forcing `-N1` took 17.99 s, and `-N2` took 13.84 s. Median sampled daemon RSS peaks were 703, 534 and 625 MiB respectively. All 56 completed module compilations in the recorded trials produced the stock artifacts. The timings use the two complete rounds. A daemon expired during the third. We retained the worker's capability default. Hadrian and the compiler worker run in separate processes. [Worker capability samples](worker-capabilities.json) · [GHC runtime options](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/runtime_control.html)
