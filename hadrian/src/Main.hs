{-# LANGUAGE CPP #-}
module Main (main) where

import Development.Shake
import Hadrian.Utilities
import Settings (newFlavourCache)
import Settings.Parser
import System.Directory (getCurrentDirectory)
import System.IO
import System.Exit
import System.Environment
import Control.Concurrent (getNumCapabilities, rtsSupportsBoundThreads, setNumCapabilities)
import Control.Exception
import Data.IORef
import qualified Crypto.Hash.SHA256 as SHA256
import qualified Data.ByteString.Base16 as Base16
import qualified Data.ByteString.Builder as Bytes
import qualified Data.ByteString.Char8 as Char8
import Data.List (isPrefixOf, sortOn)

import qualified Base
import qualified Builder
import qualified CommandLine
import qualified Flavour.Type as Flavour
import qualified Hadrian.Oracles.ArgsHash as ArgsHash
import qualified Environment
import qualified Rules
import qualified Rules.Codes
import qualified Rules.Changelog
import qualified Rules.Clean
import qualified Rules.Docspec
import qualified Rules.Documentation
import qualified Rules.Lint
import qualified Rules.Nofib
#if HADRIAN_ENABLE_SELFTEST
import qualified Rules.Selftest
#endif
import qualified Rules.SourceDist
import qualified Rules.Test
import qualified UserSettings
import qualified Progress

main :: IO ()
main = do
    -- Provide access to command line arguments and some user settings through
    -- Shake's type-indexed map 'shakeExtra'.
    argsMap <- CommandLine.cmdLineArgsMap
    flavourCache <- newFlavourCache
    case CommandLine.lookupBignum argsMap of
      Just _ -> hPutStrLn stderr $ unlines
        [ "Warning: --bignum is deprecated."
        , "  Use the '+native_bignum' flavour transformer instead (e.g. --flavour=default+native_bignum)."
        , "  When building for the JavaScript target, native bignum is now enabled automatically."
        ]
      Nothing -> return ()
    let extra = insertExtra UserSettings.buildProgressColour
              $ insertExtra UserSettings.successColour
              $ insertExtra flavourCache
              $ argsMap

        BuildRoot buildRoot = CommandLine.lookupBuildRoot argsMap

        rebuild = [ (RebuildLater, buildRoot -/- "stage0/**")
                  | CommandLine.lookupFreeze1 argsMap ||
                    CommandLine.lookupFreeze2 argsMap
                  ] ++
                  [ (RebuildLater, buildRoot -/- "stage1/**")
                  | CommandLine.lookupFreeze2 argsMap
                  ] ++
                  (if CommandLine.lookupSkipDepends argsMap
                   then [(RebuildLater, buildRoot -/- "**/.dependencies.mk"), (RebuildLater, buildRoot -/- "**/.dependencies")]
                   else [])

    singleCapability <- (== Just "1") <$> lookupEnv "HADRIAN_SINGLE_CAPABILITY"
    let buildAction build
          -- See Note [Hadrian RTS capabilities].
          | singleCapability && rtsSupportsBoundThreads =
              action $ actionBracket enter setNumCapabilities (const build)
          | otherwise = action build

        enter = do
          previous <- getNumCapabilities
          setNumCapabilities 1
          pure previous

    cwd <- getCurrentDirectory
    rawArguments <- getArgs
    persistent <- (== Just "1") <$> lookupEnv "HADRIAN_PERSISTENT_ARGS"
    let invocation = ArgsHash.ArgsInvocation persistent
            (invocationWitness cwd rawArguments (CommandLine.argumentSettingsSnapshot argsMap))
    shakeColor <- shouldUseColor
    let options :: ShakeOptions
        options = shakeOptions
            { -- Bump shakeVersion whenever a type stored in the Shake oracle
              -- changes its Binary representation (e.g. fields added/removed
              -- from PackageData or other oracle value types). This forces
              -- Shake to wipe the stale database instead of crashing on
              -- deserialisation.
              shakeVersion  = "4"
            , shakeChange   = ChangeModtimeAndDigest
            , shakeFiles    = buildRoot -/- Base.shakeFilesDir
            , shakeProgress = Progress.hadrianProgress cwd
            , shakeRebuild  = rebuild
            , shakeTimings  = False
            , shakeColor    = shakeColor
            , shakeExtra    = insertExtra invocation extra

            -- Setting shakeSymlink to False ensures files are copied out of
            -- shake's cloud cache instead of hard linked. This is important as
            -- the hard link mode makes all such files read only to avoid
            -- accidentally modifying cache files via the hard link. It turns
            -- out, many Hadrian rules attempt read access to such files and
            -- hence would in the hard link mode. These rules could be
            -- refactored to avoid write access, but setting shakeSymlink to
            -- False is a much simpler solution.
            , shakeSymlink  = False

            -- Enable linting file accesses in the build dir and ghc root dir
            -- (cwd) when using the `--lint-fsatrace` option.
            , shakeLintInside = [ cwd, buildRoot ]
            , shakeLintIgnore =
                -- Ignore access to the package database caches.
                -- They are managed externally by the ghc-pkg tool.
                [ buildRoot -/- "**/package.conf.d/package.cache"

                -- Ignore access to autom4te.cache directories.
                -- They are managed externally by auto tools.
                , "//autom4te.cache/**"

                -- Ignore in-tree GMP objects
                , buildRoot -/- "**/gmp/objs/**"
                ]
            , shakeOutput = \v -> case v of
                -- We don't want to print internal shake diagnostic messages as
                -- they are too verbose to be of any use. See #20484.
                Diagnostic -> const (pure ())
                _ -> shakeOutput shakeOptions v
            }

        rules :: Rules ()
        rules = do
            Rules.buildRules
            Rules.Docspec.docspecRules
            Rules.Documentation.documentationRules
            Rules.Clean.cleanRules
            Rules.Codes.codesRules
            Rules.Lint.lintRules
            Rules.Nofib.nofibRules
            Rules.oracleRules
#if HADRIAN_ENABLE_SELFTEST
            Rules.Selftest.selftestRules
#endif
            Rules.Changelog.changelogRules
            Rules.SourceDist.sourceDistRules
            Rules.Test.testRules
            Rules.toolArgsTarget

    -- This IORef is used to communicate the result of shake parsing
    -- command line options (which happens in shakeArgsOptionsWith, but
    -- isn't exposed to the user) to the exception handler, which uses the
    -- verbosity and colour information to decide how much of the error to display.
    shake_opts_var <- newIORef options
    handleShakeException shake_opts_var $ shakeArgsOptionsWith options CommandLine.optDescrs $ \shake_opts _ targets -> do
        writeIORef  shake_opts_var shake_opts
        let targets' = filter (not . null) $ removeKVs targets
        Environment.setupEnvironment
        return . Just $ (shake_opts, case targets' of
            [] -> rules >> buildAction Rules.topLevelTargets
            _ | singleCapability -> buildAction (need targets') >> withoutActions rules
              | otherwise -> want targets' >> withoutActions rules)

-- | Identify the inputs which argument expressions read outside Shake.
-- Read the effective directory after Shake applies --directory.
invocationWitness :: FilePath -> [String] -> String -> Action (Maybe String)
invocationWitness initialDirectory argv settings = do
    flavour <- CommandLine.cmdFlavour
    unitHash <- CommandLine.cmdUnitIdHash
    bignum <- CommandLine.cmdBignum
    options <- getShakeOptions
    let supported = "perf+no_profiled_libs"
        customBase = any ((`isPrefixOf` supported) . Flavour.name) UserSettings.userFlavours
    if flavour /= Just supported || customBase || not (null UserSettings.userPackages)
        || unitHash || bignum /= Nothing
        || shakeShare options /= Nothing || not (null (shakeCloud options))
        then pure Nothing
        else liftIO $ do
            executable <- Builder.fileSHA256 "/proc/self/exe"
            effectiveDirectory <- getCurrentDirectory
            -- Preserve the first and last values of repeated names.
            environment <- sortOn fst <$> getEnvironment
            let digest identity = Char8.unpack . Base16.encode . SHA256.hashlazy . Bytes.toLazyByteString
                    . Bytes.stringUtf8 $ show (identity, initialDirectory, effectiveDirectory, argv, settings, environment)
            pure (digest <$> executable)

{- Note [Hadrian RTS capabilities]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Shake sets the number of RTS capabilities to the job count before it runs the
target actions. For incremental builds, a single capability can reduce the
time Hadrian spends checking dependencies. Set the capability count inside
the action so that Shake keeps its job pool. Restore the count when the
action finishes or throws an exception.
-}
handleShakeException :: IORef ShakeOptions -> IO a -> IO a
handleShakeException shake_opts_var shake_run = do
  args <- getArgs
  -- Using withArgs here is a bit of a hack but the API doesn't allow another way
  -- See https://github.com/ndmitchell/shake/issues/811
  -- Passing --exception means shake throws an exception rather than
  -- catching ShakeException and displaying the error itself to the user.
  catch (withArgs ("--exception" : args) $ shake_run) $ \(_e :: ShakeException) -> do
    shake_opts <- readIORef shake_opts_var
    let
      FailureColour col = lookupExtra red (shakeExtra shake_opts)
      esc = if shakeColor shake_opts then escape col else id
    if shakeVerbosity shake_opts >= Verbose
      then
        hPrint stderr _e
      else
        -- The SomeException here is normally an IOError which lacks
        -- very much structure, in the future we could try to catch
        -- a more structured exception and further refine the
        -- displayed output. https://github.com/ndmitchell/shake/pull/812
        hPrint stderr (shakeExceptionInner _e)
    hPutStrLn stderr (esc "Build failed.")
    exitFailure

escForeground :: String -> String
escForeground code = "\ESC[" ++ code ++ "m"

escNormal :: String
escNormal = "\ESC[0m"

escape :: String -> String -> String
escape code x = escForeground code ++ x ++ escNormal
