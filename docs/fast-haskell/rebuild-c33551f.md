# GHC 10 rebuild measurements for worker c33551f

These experiments used GHC 10.1.20261115.1 at `945ea7a737` on x86-64 WSL2. Both development worker paths now select `c33551f`. The previously measured linked-compiler edit took 41.26 s with the stock configuration, 19.64 s with one Hadrian capability, and 11.67 s when a warm worker also handled the scan. Those three medians came from an earlier worker release. The comparison below measures the dependency scans for the new release separately. [Earlier end-to-end measurements](PERFORMANCE.md#linked-rebuild-with-the-hadrian-runtime-option) · [Samples and correctness checks](rebuild-c33551f.json)

## Worker release

| Direct dependency scan, 956 modules | Underlying stock GHC | Fresh worker, populated disk cache | Hot unchanged worker |
| --- | ---: | ---: | ---: |
| Stage0 | 9.98 s | 6.15 s (1.62×) | 0.544 s |
| Stage1 | 25.65 s | 11.68 s (2.20×) | 0.676 s |

The Stage0 timing compares three pairs of previous and corrected workers plus four stock calls. Only one warm repeat per worker was timed in that experiment. Stage0 linked the GHC 10 API archive used by its stock compiler. Commit `8308b28` contains the measured runtime change. Release commit `c33551f` added a regression check and changelog. The exact packaged release repeated the prefilled scan in 6.37 s between stock calls of 9.71 s and 11.26 s. The previous worker took 7.41 s on a prefilled restart and 10.47 s on first fill. The corrected worker took 6.15 s and 9.80 s respectively. Sampled median peak daemon RSS on a prefilled scan rose from 549 to 571 MiB. The Stage1 results use two order-balanced pairs on the exact release. Its first fill took 24.26 s.

The corrected worker reuses 848 parses, up from 828. It checks valid buffers for markers once and recognizes hash lines without a quoted filename. GHC accepts some noncanonical UTF-8 encodings of the start of a line marker. The old worker could miss a dependency if the named file appeared after the first scan. The new worker asks GHC to parse such input. Both releases passed stock comparisons for the creation and deletion of each marker target in a live worker, after restart with a disk cache, and after restart without one. Dependency files, backups and diagnostics matched in the release checks.

Fresh preprocessing changed the bytes of 104 of the remaining 108 buffers on an identical-input repeat. A research comparison could account for all 104 differences by removing the generated temporary directory from quoted preprocessor header markers. The ordered list of extra source files matched in all 108 cases. Parsing those modules took 1.29 and 1.33 s. That bounds the time a more permissive parse cache could save on these two scans, before validation costs. A file named by a marker can appear and disappear while the source bytes stay identical. Changing the current directory can change that result. Warning settings also changed the diagnostics and exit status for identical input. Deleting a CPP header failed during preprocessing. A new cache entry would have to preserve these outcomes.

## Linked GHC rebuild

The benchmark changes the body of `GHC.Cmm.Pipeline` and builds `stage2:exe:ghc-bin` with `--freeze1 --flavour=quick -j3`. Both linker arms used one Hadrian RTS capability and the active Stage0 worker for dependency scans. Two pairs ran in opposite orders on CPUs 20–23. Each edited build ran eight external builder actions.

| Wall time | GNU BFD | mold 2.30.0 |
| --- | ---: | ---: |
| Edit, first pair | 11.12 s | 10.21 s |
| Edit, reverse pair | 10.91 s | 9.79 s |
| First unchanged invocation, first pair | 4.62 s | 7.50 s |
| First unchanged invocation, reverse pair | 4.89 s | 7.97 s |

The faster linker saved 0.91 and 1.12 s on the edit. Both mold runs copied the GHC package and refreshed its package database again on the next unchanged invocation. BFD ran zero builders. The edit and next check together took 1.97 and 1.96 s longer with mold. A second unchanged invocation with mold ran zero builders in 5.39 and 4.67 s. This experiment used per-package GHC link flags for the GHC library and executable. No compiler selector was switched.

All 15 artifacts unaffected by linker layout matched byte for byte, including the static archive. Both linker outputs had the same exported symbols, ordered shared-library dependencies, search paths and library name. The ordinary optimized consumer and a dynamically linked GHC API consumer both returned 156. The latter initialized a GHC session with the just-built library. Its object and interface matched across linkers.

**Correction to the earlier linked-compiler checks.** The relocated benchmark tree still contained a Cabal setup configuration with the original build path. The installed GHC shared library found by the default loader came from the original tree. The earlier consumer result of 156 and the comparison of 17 on-disk build artifacts remain valid. That consumer did not verify execution of the freshly linked shared library. The new API test explicitly selects the freshly linked library and checks the resolved file. The timing results refer to a development build with reused Stage0 prerequisites.

### Fix for the repeated package copy

A GHC package has separate stamps for its vanilla and dynamic libraries. Package registration requests both in parallel. The vanilla rule also wrote the dynamic stamp. When the shared library linked before the static archive finished, the vanilla rule overwrote the timestamp Shake had recorded for the dynamic rule. The next build detected that change and repeated package installation and registration. Commit `ba31db324e` gives each stamp one writer. A direct request to rebuild only the vanilla stamp changed the dynamic stamp with the original rule. With the exact branch Hadrian, the dynamic stamp kept its timestamp and SHA-256 digest. [Stamp rule](../../hadrian/src/Rules/Library.hs)

A private benchmark correction told Cabal to copy the library from the actual build directory. Each compiler and each dynamically linked API consumer then loaded the expected GHC library through its default search path. We checked the ELF build IDs against the newly linked files. With just the Cabal correction, the mold edit took 9.33 s and the next invocation still took 7.89 s with an extra package refresh. Changing the stamp rule removed that refresh.

| With the stamp fix and active scan worker | BFD edit / next check | mold edit / next check |
| --- | ---: | ---: |
| mold first | 11.51 / 4.75 s | 9.53 / 4.84 s |
| BFD first | 12.72 / 4.99 s | 9.13 / 4.68 s |

The median edit took 12.12 s with BFD and 9.33 s with mold (1.30×). The median of edit plus first unchanged check fell from 16.99 s to 14.09 s (17.0% less time). All four unchanged checks ran zero builders. These are the two linker choices with the stamp fix in both arms. The full timing trial used a diagnostic Hadrian with the Cabal copy correction and the same single-writer behavior. The direct stamp regression used a separate build of the exact branch change. All edits ran eight builders and regenerated one of 956 dependency rows. Both consumers passed, and all 15 artifacts unaffected by linker layout agreed.

To repeat the linker trial with a matching Linux development toolchain, add the following two arguments to the linked-compiler build command. Set `MOLD_BINDIR` to the absolute directory containing `ld.mold`.

```sh
"stage1.ghc.ghc.link.opts += -optl-B${MOLD_BINDIR}/ -optl-fuse-ld=mold" \
"stage1.ghc-bin.ghc.link.opts += -optl-B${MOLD_BINDIR}/ -optl-fuse-ld=mold"
```

### Link and archive costs

We replayed the recorded link commands on four distinct physical cores. The GHC shared library used 890 dynamic objects. The driver used ten. Three rounds rotated the order of the four linkers. Each run forced a fresh link. All four drivers loaded their own rebuilt library and compiled an optimized consumer to the same interface, object and executable.

| Median forced link | BFD | gold | LLD 17 | mold 2.30 |
| --- | ---: | ---: | ---: | ---: |
| GHC shared library | 2.206 s | 1.360 s | 0.740 s | 0.511 s |
| GHC executable | 0.933 s | 0.415 s | 0.233 s | 0.214 s |

BFD, LLD and mold produced the same 90,845 external symbol descriptions for the library. Gold added three linker-defined symbols. In a separate process sample, BFD used one thread and reached about 447 MiB RSS. The busiest mold process used four threads and reached about 433 MiB with its default settings. These are sampled peaks for individual linker processes and descendants, excluding the GHC driver. [LLD](https://lld.llvm.org/) · [mold options](https://github.com/rui314/mold/blob/main/docs/mold.md)

Repacking the 890 static objects in a GNU thin archive took 0.332 s median over four runs, versus 0.607 s for the ordinary archive. The thin archive occupied 6,352,466 bytes and referred to the original objects. The ordinary archive occupied 215,915,674 bytes and matched the retained stock archive byte for byte. Linking all members into a relocatable object produced identical bytes in both cases. Archive creation overlaps the shared-library link during the full build. Using a thin archive for installation would also require preserving its object paths. [GNU ar](https://sourceware.org/binutils/docs/binutils/ar.html)

### Routing compilation through the worker

In a private Hadrian trial on worker `fa68e89`, one warm matched edit took 11.73 s with the worker handling dependency scans and 12.71 s when it also handled Haskell compilation. Hadrian ran three compile rules, but GHC skipped code generation for both importers. Only `GHC.Cmm.Pipeline` generated code. The previous 5.12× result for a single object target therefore did not transfer to this linked edit. The development integration continues to send only dependency commands to the worker.

In this trial the warmed worker changed 19 local string-label names in the object's ELF string table. Instructions, data and relocation targets agreed. A two-literal fixture reproduced the label difference. With `-fobject-determinism`, the fixture's ordinary and dynamic objects matched stock exactly.

## Reuse inside an optimized Core binding

We tested a cache check before the first simplifier visit to a nonrecursive binding. Both the instrumented and stock compilers still ran the full optimizer. Recording the binding input and rewrite rules for its direct free identifiers detected additions, removals, phase changes and RHS changes for an immediately visible rule. It also detected a changed unfolding for a real GHC binding. It missed a change when the caller used an unchanged wrapper. Inlining introduced a rule head that the original expression did not mention. Adding an orphan rule for that head changed the executable result from 6 to 46 while the initial cache check still agreed.

Replaying the previous visit's external rule lookups detected this case before simplification. An unrelated orphan rule preserved the result 6. Adding the rule on the inlined target changed exactly that head's rule description. On the fixture the check resolved all five previously observed external identifiers. Two local observations still prevented reuse. On `GHC.Utils.Misc.doesDirNameExist` it resolved all eight external identifiers from the first visit. Four local observations prevented reuse. All five instrumented compilations matched the corresponding stock object and interface.

The real binding's precheck took 14.5–20.7 ms and allocated about 26 MB. An earlier trace attributed 15.52 MB to simplifying this binding in the first iteration. It used printed Core and two levels of unfolding traversal as a diagnostic. A production cache would need a cheaper stable encoding, a way to validate local observations, and tests for substitution, fresh names, phases and floated bindings. No optimizer work was skipped in this experiment.

On the benchmark host, the replay kit is in `_build/fast-haskell/core-rule-probe-c33551f/` in the incremental-builds worktree. It contains the diagnostic patch for the measured GHC revision and the standalone counterexample. The fixture discovers its inputs from a previous run and verifies the optimized object and interface at each edit. The research data above includes the resulting hashes and verdicts.
