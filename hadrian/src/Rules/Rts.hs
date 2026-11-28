module Rules.Rts (rtsRules, rtsRustObjects) where

import Hadrian.Oracles.ArgsHash (trackArgsHash)
import Hadrian.Target (target)
import Hadrian.Utilities
import Settings.Builders.Common

-- | This rule has priority 3 to override the general rule for generating shared
-- library files (see Rules.Library.libraryRules).
rtsRules :: Rules ()
rtsRules = priority 3 $ do
    root <- buildRootRules
    -- Solve the recursive dependency between the rts and ghc-internal
    -- on Windows by creating an import lib for the ghc-internal dll,
    -- to be linked into the rts dll.
    forM_ [Stage1, Stage2, Stage3 ] $ \ stage -> do
        let buildPath = root -/- buildDir (rtsContext stage)
        -- allWays omits these two combined RTS ways.
        -- See Note [Closure size build constants] in rts/rust/ClosureSizeConstants.c.
        forM_ (map wayFromUnits (subsequences [minBound .. maxBound])) $ \rtsWay -> do
            forM_ [ ("closure-size", "closure_size", "ClosureSizeConstants", "CLOSURE_SIZE_LAYOUT_RS")
                  , ("heap-pointers", "heap_pointers", "HeapPointerConstants", "HEAP_POINTER_LAYOUT_RS")
                  ] $ \(stem, crate, probeName, layoutEnv) -> do
                let probe  = buildPath -/- ("c/rust/" ++ probeName ++ ".") ++ osuf rtsWay
                    layout = buildPath -/- (stem ++ "-layout-") ++ show rtsWay ++ ".rs"
                    rustObject = buildPath -/- ("rust-rts-" ++ stem ++ "-") ++ show rtsWay ++ ".o"
                layout %> \output -> do
                    need [probe, sourcePath -/- "Rules/Rts.hs"]
                    nmPath <- builderPath (Nm stage)
                    nm <- exeSpawnPath nmPath
                    Stdout symbols <- cmdExe nm ["-P", "-t", "d", "-S", probe]
                    constants <- mapM parseRustLayoutConstant
                        [line | line <- lines symbols, "ghc_rust_" `isPrefixOf` line]
                    when (null constants) $ fail $ "No Rust layout constants in " ++ probe
                    writeFileAtomic output (unlines constants)
                rustObject %> \output -> do
                    need [layout]
                    layoutPath <- liftIO $ makeAbsolute layout
                    let modules = if stem == "closure-size"
                            then ["rts/rust/compact.rs", "rts/rust/nonmoving.rs"]
                            else ["rts/rust/mutable_list.rs"]
                    buildRustRtsWithEnv [AddEnv layoutEnv layoutPath]
                        stage ("ghc_rts_" ++ crate) ("rts/rust/" ++ crate ++ ".rs") modules [] output
        buildPath -/- "rust-rts.o" %> \output -> do
            largeAddressSpace <- rtsConfigDefines buildPath "USE_LARGE_ADDRESS_SPACE"
            let rustCfg = if largeAddressSpace then ["--cfg", "ghc_use_large_address_space"] else []
            buildRustRts stage "ghc_rts" "rts/rust/lib.rs"
                [ "rts/rust/adjustor_slots.rs"
                , "rts/rust/alloc_array.rs"
                , "rts/rust/archive_member.rs"
                , "rts/rust/block_count.rs"
                , "rts/rust/c_finalizers.rs"
                , "rts/rust/cafs.rs"
                , "rts/rust/closure_table.rs"
                , "rts/rust/clone_stack.rs"
                , "rts/rust/arena.rs"
                , "rts/rust/encode.rs"
                , "rts/rust/exec_page.rs"
                , "rts/rust/eventlog_file_writer.rs"
                , "rts/rust/file_lock.rs"
                , "rts/rust/finalizer_batch.rs"
                , "rts/rust/foreign_exports.rs"
                , "rts/rust/gc_budget.rs"
                , "rts/rust/hash_chain.rs"
                , "rts/rust/hash_insert.rs"
                , "rts/rust/hash_walk.rs"
                , "rts/rust/incall.rs"
                , "rts/rust/liveness.rs"
                , "rts/rust/mark_count.rs"
                , "rts/rust/mark_weak.rs"
                , "rts/rust/mblock_extents.rs"
                , "rts/rust/prim_float.rs"
                , "rts/rust/pool.rs"
                , "rts/rust/stable_name.rs"
                , "rts/rust/stable_ptr.rs"
                , "rts/rust/static_ptr_table.rs"
                , "rts/rust/suspended_calls.rs"
                , "rts/rust/sweep.rs"
                , "rts/rust/thread_label.rs"
                , "rts/rust/timeout_queue.rs"
                , "rts/rust/top_handler.rs"
                ] rustCfg output
        buildPath -/- "rust-rts-prim-bits.o" %>
            buildRustRts stage "ghc_rts_prim_bits" "rts/rust/prim_bits.rs" [] []
        buildPath -/- "rust-rts-check-vector-support.o" %>
            buildRustRts stage "ghc_rts_check_vector_support" "rts/rust/check_vector_support.rs" [] []
        buildPath -/- "rust-rts-pathdir.o" %>
            buildRustRts stage "ghc_rts_pathdir" "rts/rust/pathdir.rs" [] []
        buildPath -/- "rust-rts-posix-getenv.o" %>
            buildRustRts stage "ghc_rts_posix_getenv" "rts/rust/posix_getenv.rs" [] []
        buildPath -/- "rust-rts-profiler-json.o" %>
            buildRustRts stage "ghc_rts_profiler_json" "rts/rust/profiler_json.rs" [] []
        buildPath -/- "rust-rts-poll-slots.o" %>
            buildRustRts stage "ghc_rts_poll_slots" "rts/rust/poll_slots.rs" [] []
        buildPath -/- "rust-rts-spark-retain.o" %>
            buildRustRts stage "ghc_rts_spark_retain" "rts/rust/spark_retain.rs" [] []
        buildPath -/- "rust-rts-wsdeque.o" %>
            buildRustRts stage "ghc_rts_wsdeque" "rts/rust/wsdeque.rs" [] []
        buildPath -/- "libHSghc-internal-*.def" %> buildGhcInternalImportDef
        buildPath -/- "libHSghc-internal-*.dll.a" %> buildGhcInternalImportLib stage

-- | Return the Rust objects for an RTS library way.
rtsRustObjects :: Stage -> Way -> Action [FilePath]
rtsRustObjects stage way = do
    rustc <- rtsRustCompiler stage
    if null rustc then pure [] else do
        path <- rtsBuildPath stage
        poll <- if Threaded `wayUnit` way
            then pure False
            else rtsConfigDefines path "IOMGR_BUILD_POLL"
        let flags = target (rtsContext stage) (Cabal Flags stage) [] []
        trackArgsHash flags
        rustTsanSafe <- notElem "thread-sanitizer" <$> interpret flags getArgs
        let rustDeque = Threaded `wayUnit` way && rustTsanSafe
        pure $ [path -/- "rust-rts.o", path -/- "rust-rts-prim-bits.o"]
            ++ [path -/- "rust-rts-closure-size-" ++ show way ++ ".o" | rustTsanSafe]
            ++ [path -/- "rust-rts-heap-pointers-" ++ show way ++ ".o" | rustTsanSafe]
            ++ [path -/- "rust-rts-check-vector-support.o" | rustTsanSafe]
            ++ [path -/- "rust-rts-pathdir.o" | rustTsanSafe]
            ++ [path -/- "rust-rts-posix-getenv.o" | rustTsanSafe]
            ++ [path -/- "rust-rts-profiler-json.o" | Profiling `wayUnit` way]
            ++ [path -/- "rust-rts-poll-slots.o" | poll]
            ++ [path -/- "rust-rts-spark-retain.o" | Threaded `wayUnit` way]
            ++ [path -/- "rust-rts-wsdeque.o" | rustDeque]

-- | Check an RTS feature macro in the generated configuration.
rtsConfigDefines :: FilePath -> String -> Action Bool
rtsConfigDefines path name = do
    autoconf <- readFile' (path -/- "include/ghcautoconf.h")
    pure $ any ((== ["#define", name, "1"]) . words) (lines autoconf)

-- | Compile a Rust RTS crate to a PIC object.
buildRustRts :: Stage -> String -> FilePath -> [FilePath] -> [String] -> FilePath -> Action ()
buildRustRts = buildRustRtsWithEnv []

buildRustRtsWithEnv :: [CmdOption] -> Stage -> String -> FilePath -> [FilePath] -> [String] -> FilePath -> Action ()
buildRustRtsWithEnv env stage crate source modules extraArgs output = do
    rustc <- rtsRustCompiler stage
    when (null rustc) $ fail "The Rust RTS requires --enable-rust-rts."
    _ <- setting RustRtsCompilerVersion
    need [sourcePath -/- "Rules/Rts.hs"]
    need (rustc : source : modules)
    createDirectory (takeDirectory output)
    prog <- exeSpawnPath rustc
    cmdExe prog env $
        [ "--edition=2024", "--crate-name=" ++ crate, "--crate-type=lib"
        , "--target=x86_64-unknown-linux-gnu", "--emit=obj"
        , "-Cpanic=abort", "-Crelocation-model=pic", "-Ccodegen-units=1"
        , "-Copt-level=2", "-o", output, source
        ] ++ extraArgs

-- | Decode a size from one line of POSIX nm output with decimal values.
parseRustLayoutConstant :: String -> Action String
parseRustLayoutConstant line = case words line of
    [symbol, _kind, _address, rawSize]
        | Just typedName <- stripPrefix "ghc_rust_" symbol
        , (ty, '_':name) <- break (== '_') typedName
        , ty `elem` ["u32", "usize"]
        , [(size, "")] <- reads rawSize
        , size > (0 :: Integer)
        -> pure $ "const " ++ name ++ ": " ++ ty ++ " = " ++ show (size - 1) ++ ";"
    _ -> fail $ "Invalid Rust layout constant in target nm output: " ++ line

buildGhcInternalImportDef :: FilePath -> Action ()
buildGhcInternalImportDef target = do
    templateIn <- readFile' "rts/win32/libHSghc-internal.def.in"
    let dllName = takeFileName target -<.> "dll"
        templateOut = replace "@GhcInternalDll@" dllName templateIn
    writeFileAtomic target templateOut

buildGhcInternalImportLib :: Stage -> FilePath -> Action ()
buildGhcInternalImportLib stg target = do
    let input = dropExtensions (dropExtension target) <.> "def" -- the .def file
        output = target -- the .dll.a import lib
    need [input]
    runBuilder (Dlltool stg) ["-d", input, "-l", output] [input] [output]
