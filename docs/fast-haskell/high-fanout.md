# Incremental GHC builds after an edit with many importers

The speedup patches live on `incremental-builds`. The initial measurements use the `dependent-haskell` compiler at `945ea7a737` (GHC 10.1.20261115.1). The target was `stage2:exe:ghc-bin` with `--flavour=quick --freeze1 -j3` on x86-64 WSL2. [Measurements and artifact comparisons](high-fanout.json)

## Rechecking importers

We changed the upper bound on one branch of the edit-distance implementation in `GHC.Utils.Misc` from 32 to 31. Hadrian scheduled the producer, 298 ordinary importer objects and six boot objects. On a smaller benchmark, `GHC.Cmm.Pipeline` had only two direct importers.

The first edited build took 48.35 s, including a cold worker dependency scan. Hadrian ran 305 Haskell compile commands. Only the edited module generated code. GHC reported that all 304 importers were up to date. We hashed both objects and both interfaces for the producer and all 298 ordinary direct importers. Only the producer's files changed. The next build took 5.95 s and ran zero builders. The installed GHC shared library had the build ID of the new build output, and the linked GHC API consumer returned 156.

A second experiment kept one Hadrian capability, three build jobs and worker `c33551f` for the dependency scan throughout. A private Hadrian could also route single-file Haskell compilation to the Stage0 worker. The two edits used to prime the arms took 43.96 s and 39.38 s. Each timed arm subsequently saw each source version once.

| Handling of the 305 compilation requests | Source A | Source B | Median | Median following no-op |
| --- | ---: | ---: | ---: | ---: |
| Ordinary GHC | 35.16 s | 31.72 s | 33.44 s | 4.83 s |
| Persistent worker | 26.51 s | 25.50 s | 26.01 s | 5.22 s |

The median linked rebuild was **1.29× faster** with compilation routed to the worker. The difference between medians was 7.44 s. Each run recorded 304 up-to-date decisions. Each arm had one full graph hit and one partial scan that regenerated a single row. All four immediate no-ops ran zero builders. Both versions passed the consumer test with the installed library's build ID checked against the rebuilt one.

For the same source, both producer interfaces and all 1,192 measured importer artifacts matched across these two routes. The producer's ordinary and dynamic object hashes differed, as did the linked library hashes. The development integration still routes dependency scans through the worker. A narrower experiment can serve GHC's up-to-date decision in a daemon and give actual code generation to the ordinary executable.

### Let the worker check and stock GHC compile

A separate GHC 10 prototype intercepted the one-shot `T_HscRecomp` phase. When GHC reported that a module was up to date, the daemon finished the ordinary up-to-date path. Otherwise the shim ran stock GHC with the original arguments. The prototype also delegated boot modules and requests with unsupported source or compiler flags.

| Edit direction | Stock compiler | Worker checks, stock code generation |
| --- | ---: | ---: |
| Cutoff 32 to 31 | 35.55 s | 29.90 s |
| Cutoff 31 to 32 | 34.24 s | 33.49 s |

Median wall time fell from **34.90 s to 31.70 s (9.2%)** across two order-balanced pairs. Each arm used the same `c33551f` scan worker and regenerated one of 956 dependency rows. Of 305 compile requests, the daemon completed 253 up-to-date checks and delegated the other 52. The two immediate no-ops took 5.14 and 5.25 s with stock and 5.03 and 6.54 s with worker checks. Each ran zero compile, dependency, or link actions.

For each source version, 1,196 ordinary module artifacts, all 207 existing boot artifacts, the archive, shared library and compiler executable matched byte for byte. The default loader resolved the expected library in each arm, and each GHC API consumer returned 156. In a separate replay of the real `GHC.Cmm.Pipeline -O2 -dynamic-too` command, the daemon preserved stock diagnostics and artifact modification times on an unchanged compile. After an RHS edit, stock generated all four artifacts. This mode remains a private prototype. The normal Hadrian integration continues to use the worker only for dependency scans.

### What an ABI fingerprint can tell Hadrian

The `GHC.Cmm.Pipeline` body edit preserved its ABI hash while changing both its full interface hash and its object. A stock GHC 10 fixture changed a `NOINLINE` exported constant from 7 to 9. Its ABI hash stayed equal at both `-O0` and `-O2`. Ordinary importers kept their objects, and relinking produced the new result. A Template Haskell splice that evaluated the constant needed a new object in each configuration. Stock GHC reported the Template Haskell dependency and recompiled the importer. Skipping such a request solely because the imported ABI matched would preserve the old spliced value. [GHC recompilation checks](../../compiler/GHC/Iface/Recomp.hs) · [GHC guide to separate compilation](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/separate_compilation.html)

## Skipping importer checks on GHC 10.1.20261127

The same cutoff edit changed the two producer objects and preserved the information used by its importers. A private Hadrian rule took the complete static and dynamic interfaces of `GHC.Utils.Misc`, removed the derived interface hash, and set the source hash to zero. It computed a fingerprint over the remaining serialized fields, including the usage records, docs, simplified Core, and extension fields. Hadrian still built and linked the changed objects.

We selected 249 ordinary GHC modules from the 302 importer commands after reading their static and dynamic usage records. For these modules, Hadrian tracked the producer's normalized interfaces. Five boot modules and 48 modules with recorded file dependencies kept their ordinary prerequisites. Both arms used the same stage-matched worker (`ab53801`) with its validated interface cache enabled. The control tracked both complete producer interface files through the same Shake rule.

| Cutoff edit | Full interfaces | Normalized interfaces | Wall time saved |
| --- | ---: | ---: | ---: |
| 32 to 31 | 35.32 s | 27.67 s | 21.7% |
| 31 to 32 | 35.66 s | 28.75 s | 19.4% |

Each cell is one linked `stage2:exe:ghc-bin` rebuild with `perf+no_profiled_libs --freeze1 -j3` and one Hadrian capability. The control ran first in both directions. Each edit regenerated one of 943 dependency rows. Haskell compile requests fell from 303 to 54. Only the producer generated code. Both builds matched ordinary GHC for all four artifacts of the 249 selected modules, the compiler archive and shared library, the stage compiler, and a separately built and executed GHC API consumer. All four immediate repeat builds ran zero actions.

A direct ABI fingerprint would miss a re-export. In an `-O2` fixture, A used an inlined `C.f` through B. The dependency file listed only `A.o: B.hi`. Changing `f x = x + 1` to `f x = x + 2` preserved B's ABI but changed the recorded usage of C in B's interface. Skipping A on ABI equality left the executable printing 11. Stock GHC rebuilt A and printed 12. The normalized interface detected the change for both an explicit re-export and a whole-module re-export. It also detected separate changes to a documentation field and an opaque extension field. [GHC interface serialization](../../compiler/GHC/Unit/Module/ModIface.hs) · [GHC recompilation checks](../../compiler/GHC/Iface/Recomp.hs)

The next step is to derive eligibility from the current compilation instead of a fixed list of modules. The rule must track imported code used at compile time, independent file and directory dependencies, and changes to flags or imports. Measure the cost of producing these fingerprints across the build before enabling the rule for other modules.

### Native opt-in on the live dependency graph

The portable implementation is available through `HADRIAN_NORMALIZED_IFACE_WORKER` with a prepared worker that advertises interface capability v2. It discovers high-fanout providers from the Stage1 compiler dependency graph and checks the consumer's successful compile arguments and both interfaces. The package keeps ordinary dependencies when the worker cannot establish that a consumer can skip its provider's source hash.

On the rebuilt GHC 10.1.20261127 Stage0, the initial linked edit recorded 3,147 normalized edges. The warm revert ran 54 Haskell compile requests, compared with 303 when the feature was disabled. It still compiled the producer and relinked the compiler. The initial opt-out ran 249 up-to-date checks so Shake could restore ordinary dependencies. Compiler artifacts and a separately compiled dynamic consumer matched stock in each source state. This qualification shared the scheduler with other tasks. Use the cumulative comparison for latency. [Hadrian setup](../../hadrian/README.md#experimental-normalized-interface-dependencies)

With worker `e0d203b`, a later linked run regenerated one of 943 dependency rows on the warm revert and ran 54 compile requests. The seed edit had reordered the installed global cache while the active in-place cache stayed byte-identical. The seed and revert matched the stock linked compiler and dynamic consumer. Both immediate repeats ran zero build actions. In a separate replay of the captured `-M` command, the same cache reorder sent the previous worker to stock GHC in 22.32 s. The new worker regenerated one row in 0.89 s and matched the stock Makefile, backup and diagnostics. Each scan time is one shared-machine sample. The capped linked windows expired during their second measured edit, so the earlier cumulative comparison remains the paired latency result.

## Source edits before optimization

In separate checked one-shot compilations of `GHC.Utils.Misc` at `-O2`, an unchanged compile took 0.20 s. A same-line trailing comment or a change in internal spacing took 2.14–2.19 s. The source hash in the interface changed, but the printed desugared Core, printed optimized Core and native object matched. Inserting a whole comment line changed the object even with debug information off. In a runnable `HasCallStack` example, the observed source position moved from line 6 to line 7. With `-g2`, changing spacing alone changed source ticks and native bytes.

Writing simplified Core into the interface roughly doubled its size for this module. The compiler still rebuilt the edited source. Disabling its self-recompilation metadata forced even an unchanged compile. These experiments identify a candidate for object reuse after validating code-generation inputs. They also show why a comment-stripping hash cannot justify skipping optimization. [GHC compilation phase options](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/phases.html)

## Package installation

For the smaller `GHC.Cmm.Pipeline` edit, Cabal spent 1.87 s copying the compiler package in a 12.18 s linked rebuild. It rewrote 1,772 interfaces whose bytes and modes were already correct. A private change preserved 1,770 of them (37.25 MB). Over two balanced pairs the control edit took 12.10 and 13.82 s, and the candidate took 17.95 and 12.40 s. This gave no repeatable wall-time gain.

We also measured GNU strip writing the updated archive and shared library directly to temporary outputs before renaming them into place. Across two runs, their combined median fell from 1.215 s to 0.841 s. The installed files matched the ordinary copy-and-strip output byte for byte and kept their modes. This was an isolated comparison. Installing the complete package through Hadrian with this change remains unmeasured.
