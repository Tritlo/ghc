{-# LANGUAGE GADTs, TypeFamilies #-}

module Rules.Compile (compilePackage) where

import Hadrian.BuildPath
import Hadrian.Oracles.TextFile

import Base
import qualified Builder
import Context as C
import Expression
import Oracles.Flag (targetSupportsSharedLibs)
import Rules.Generate
import Settings
import Target
import Utilities

import qualified Text.Parsec as Parsec
import Control.Exception (evaluate)
import qualified Data.ByteString.Char8 as BSC
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Char (isHexDigit)
import GHC.Generics (Generic)
import Packages (compiler)
import System.IO (IOMode(ReadMode), withBinaryFile)
import System.IO.Error (tryIOError)

-- * Rules for building objects and Haskell interface files

compilePackage :: [(Resource, Int)] -> Rules ()
compilePackage rs = do
    root <- buildRootRules
    readReceipt <- normalizedImportRules root
    -- We match all file paths that look like:
    --   <root>/...stuffs.../build/...stuffs.../<something>.<suffix>
    --
    -- where:
    --   - the '...stuffs...' bits can be one or more path components,
    --   - the '<suffix>' part is a way prefix (e.g thr_p_, or nothing if
    --     vanilla) followed by an object file extension, without the dot
    --     (o, o-boot, hi, hi-boot),
    --
    -- and parse the information we need (stage, package path, ...) from
    -- the path and figure out the suitable way to produce that object file.
    alternatives $ do
      -- Language is identified by subdirectory under /build.
      -- These are non-haskell files so only have a .o or .<way>_o suffix.
      [ root -/- "**/build/c/**/*." ++ wayPat ++ "o"
        | wayPat <- wayPats] |%> compileNonHsObject rs C

      [ root -/- "**/build/cmm/**/*." ++ wayPat ++ "o"
        | wayPat <- wayPats] |%> compileNonHsObject rs Cmm

      [ root -/- "**/build/cpp/**/*." ++ wayPat ++ "o"
        | wayPat <- wayPats] |%> compileNonHsObject rs Cxx

      [ root -/- "**/build/s/**/*." ++ wayPat ++ "o"
        | wayPat <- wayPats] |%> compileNonHsObject rs Asm

      [ root -/- "**/build/S/**/*." ++ wayPat ++ "o"
        | wayPat <- wayPats] |%> compileNonHsObject rs Asm

      [ root -/- "**/build/js/**/*." ++ wayPat ++ "o"
        | wayPat <- wayPats] |%> compileNonHsObject rs JS

      -- All else is haskell.
      -- These come last as they overlap with the above rules' file patterns.

      -- When building dynamically we depend on the static rule if shared libs
      -- are supported, because it will add the -dynamic-too flag when
      -- compiling to build the dynamic files alongside the static files
      forM_ wayPats $ \wayPat -> ( root -/- ("**/build/**/*." ++ wayPat ++ "dyn_o") :& root -/- ("**/build/**/*." ++ wayPat ++ "dyn_hi") :& Nil )
        &%> \ ( dyn_o :& _dyn_hi :& _ ) -> do

          b@(BuildPath _root stage _path _o)
            <- parsePath (parseBuildObject root) "<object file path parser>" dyn_o
          p <- targetSupportsSharedLibs stage
          if p
            then do
               let ctx = objectContext b
                   way = removeWayUnit Dynamic $ C.way ctx
               -- We `need` ".o/.hi" because GHC is called with `-dynamic-too`
               -- and builds ".dyn_o/.dyn_hi" too.
               changed <- needHasChanged [dyn_o -<.> osuf way, dyn_o -<.> hisuf way]

               -- If for some reason a previous Hadrian execution has been
               -- interrupted after the rule for .o/.hi generation has completed
               -- but before the current rule for .dyn_o/.dyn_hi has completed,
               -- or if some of the dynamic artifacts have been removed by the
               -- user, "needing" the non dynamic artifacts is not enough as
               -- Shake won't execute the associated action. Hence we detect
               -- this case and we explicitly build the dynamic artifacts here:
               case changed of
                  [] -> compileHsObjectAndHi readReceipt rs dyn_o
                  _  -> pure ()

            else compileHsObjectAndHi readReceipt rs dyn_o

      forM_ ((,) <$> hsExts <*> wayPats) $ \ ((oExt, hiExt), wayPat) ->
        (  (root -/- "**/build/**/*." ++ wayPat ++ oExt)
        :& (root -/- "**/build/**/*." ++ wayPat ++ hiExt)
        :& Nil ) &%>
          \ ( o :& _hi :& _ ) ->
            compileHsObjectAndHi readReceipt rs o
  where
    hsExts = [ ("o", "hi")
             , ("o-boot", "hi-boot")
             ]
    wayPats = [ "", "*_" ]

-- | Cache the candidate list for a package dependency graph.
newtype HighFanout = HighFanout (FilePath, FilePath) deriving (Eq, Generic, Show)
instance Binary HighFanout
instance Hashable HighFanout
instance NFData HighFanout
type instance RuleResult HighFanout = Set.Set FilePath

-- | Only this stage and package are qualified for the first experiment.
normalizedImportRules :: FilePath -> Rules (FilePath -> Action (Maybe (String, [String])))
normalizedImportRules root = do
    void $ addOracleCache $ \(HighFanout (depFile, directory)) -> do
      need [depFile]
      contents <- liftIO $ BSC.readFile depFile
      let rows = map (words . BSC.unpack) (BSC.lines contents)
      pure . Map.keysSet . Map.filter ((>= 64) . Set.size) . Map.fromListWith Set.union $
        [ (iface, Set.singleton obj)
        | obj : src : deps <- rows
        , takeExtension obj == ".o", takeExtension src == ".hs"
        , directory `isPathPrefix` obj
        , iface <- deps
        , takeExtension iface == ".hi", directory `isPathPrefix` iface
        ]
    let directory = root -/- "stage1/compiler/build"
        depFile = root -/- "stage1/compiler/.dependencies"
    (root -/- "stage1/compiler/build//*.normalized-import") %> \stamp -> do
      let static = stamp -<.> "hi"
          dynamic = stamp -<.> "dyn_hi"
      need [static]
      selected <- Builder.builderPath (Ghc CompileHs Stage1) >>= Builder.normalizedIfaceWorker
      hasDynamic <- doesFileExist dynamic
      when hasDynamic $ need [dynamic]
      evidence <- case selected of
        Just (daemon, libdir, _) | hasDynamic -> do
          providers <- askOracle (HighFanout (depFile, directory))
          if static `Set.member` providers
            then do
              need [daemon]
              Builder.ifaceWorkerQuery daemon ["fingerprint", "--evidence", libdir, static, dynamic]
            else pure []
        _ -> pure []
      receipt <- case (selected, parseProvider evidence) of
        (Just (_, _, digest), Just _) -> pure (("helper-v1 " ++ digest) : evidence)
        _ -> do
          staticHash <- rawHash static
          dynamicHash <- if hasDynamic then rawHash dynamic else pure "missing"
          pure ["raw-iface-v1 " ++ staticHash ++ " " ++ dynamicHash]
      writeFileChanged stamp (unlines receipt)
    -- Share the read and parse among all consumers of this provider.
    -- A strict read closes the descriptor before the consumer can suspend.
    newCache $ \stamp -> do
      need [stamp]
      liftIO $ do
        contents <- BSC.readFile stamp
        let receipt = case map BSC.unpack (BSC.lines contents) of
              tag : evidence -> (,) tag <$> parseProvider evidence
              _ -> Nothing
        evaluate (rnf receipt `seq` receipt)
  where
    rawHash path = liftIO (Builder.fileSHA256 path) >>= maybe
      (fail ("cannot read raw interface " ++ path)) pure

isPathPrefix :: FilePath -> FilePath -> Bool
isPathPrefix dir path = addTrailingPathSeparator dir `isPrefixOf` path

parseProvider :: [String] -> Maybe [String]
parseProvider [digest, provider]
  | ["normalized-iface-v1", static, dynamic] <- words digest
  , all isFingerprint [static, dynamic]
  , ["provider", home, unit, name, staticAbi, dynamicAbi] <- splitOn "\t" provider
  , all (not . null) [home, unit, name]
  , all isFingerprint [staticAbi, dynamicAbi] = Just [home, unit, name, staticAbi, dynamicAbi]
parseProvider _ = Nothing

isFingerprint :: String -> Bool
isFingerprint hash = length hash == 32 && all isHexDigit hash

-- | Convert the daemon rows into a set to check multiple potential providers.
parseConsumer :: [String] -> Maybe (Set.Set [String])
parseConsumer ("iface-evidence-v2" : rows) = Set.fromList <$> traverse parse rows
  where
    parse row
      | fields@[way, kind, unit, name, abi] <- splitOn "\t" row
      , way `elem` ["static", "dynamic"], kind `elem` ["home", "package"]
      , all (not . null) [unit, name], isFingerprint abi = Just fields
      | otherwise = Nothing
parseConsumer _ = Nothing

-- | Require the current provider's recorded ABI in both consumer ways.
matchesProvider :: Set.Set [String] -> [String] -> Bool
matchesProvider uses [home, unit, name, sAbi, dAbi] =
    matches "static" sAbi && matches "dynamic" dAbi
  where
    matches way abi = [way, "home", home, name, abi] `Set.member` uses
                   || [way, "package", unit, name, abi] `Set.member` uses
matchesProvider _ _ = False

{- Note [Normalized importer dependencies]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Only opt-in Stage1 compiler vanilla object rules can substitute an input
receipt for a raw interface. The normal dependency list still names the
provider. The order-only receipt makes both provider ways available before
the compiler runs. If the pair cannot be verified, the original raw
dependency is used before compilation.
The consumer's own interfaces are outputs of this action. Read them only
after normal compilation, and never need them from this rule. A certificate
must match a current provider in both ways. Keep the ordinary raw dependency
if any evidence is missing or invalid. A receipt has a normal dependency on
the worker selection and records the helper digest in its content. If the mode is disabled or the release moves, it can
revert to raw bytes before Shake decides whether a stored consumer is clean.
-}

-- | Recognize common CPP pragmas before starting the interface helper.
-- A match keeps the raw dependencies. The helper checks all other sources.
hasCppPragmaPrefix :: FilePath -> IO Bool
hasCppPragmaPrefix path = do
    contents <- tryIOError (withBinaryFile path ReadMode (\h -> BSC.hGet h 4096))
    pure (either (const False) (any cppLine . BSC.lines) contents)
  where
    cppLine line =
        let trimmed = BSC.dropWhile (\c -> c == ' ' || c == '\t') line
        in any (\prefix -> BSC.isPrefixOf prefix trimmed) (map BSC.pack ["{-# LANGUAGE CPP ", "{-# OPTIONS_GHC -cpp "])

-- * Object file paths types and parsers

{- We are using a non uniform representation that separates
   object files produced from Haskell code and from other
   languages, because the two "groups" have to be parsed
   differently enough that this would complicated the parser
   significantly.

   Indeed, non-Haskell files can only produce .o (or .thr_o, ...)
   files while Haskell modules can produce those as well as
   interface files, both in -boot or non-boot variants.

   Moreover, non-Haskell object files live under:
     <root>/stage<N>/<path/to/pkg>/build/{c,cmm,s}/

   while Haskell object/interface files live under:
     <root>/stage<N>/<path/to/pkg>/build/

   So the kind of object is partially determined by
   whether we're in c/, cmm/ or s/ but also by the
   object file's extension, in the case of a Haskell file.
   This could have been addressed with some knot-tying but
   Parsec's monad doesn't give us a MonadFix instance.

   We therefore stick to treating those two type of object
   files non uniformly.
-}

-- | Non Haskell source languages that we compile to get object files.
data SourceLang = Asm | C | Cmm | Cxx | JS deriving (Eq, Show)

parseSourceLang :: Parsec.Parsec String () SourceLang
parseSourceLang = Parsec.choice
  [ Parsec.string "js" *>  pure JS
  , Parsec.char 'c' *> Parsec.choice
      [ Parsec.string "mm" *> pure Cmm
      , Parsec.string "pp" *> pure Cxx
      , pure C
      ]
  , Parsec.char 's' *> pure Asm
  ]

type Basename = String

parseBasename :: Parsec.Parsec String () Basename
parseBasename = Parsec.manyTill Parsec.anyChar (Parsec.try $ Parsec.char '.')

-- | > <c|cmm|s>/<file>.<way prefix>_o
data NonHsObject = NonHsObject SourceLang Basename Way
  deriving (Eq, Show)

parseNonHsObject :: Parsec.Parsec String () NonHsObject
parseNonHsObject = do
    lang <- parseSourceLang
    _ <- Parsec.char '/'
    file <- parseBasename
    way <- parseWayPrefix vanilla
    _ <- Parsec.char 'o'
    return (NonHsObject lang file way)

-- | > <o|hi|o-boot|hi-boot>
data SuffixType = O | Hi | OBoot | HiBoot deriving (Eq, Show)

parseSuffixType :: Parsec.Parsec String () SuffixType
parseSuffixType = Parsec.choice
  [ Parsec.char 'o' *> Parsec.choice
      [ Parsec.string "-boot" *> pure OBoot
      , pure O
      ]
  , Parsec.string "hi" *> Parsec.choice
      [ Parsec.string "-boot" *> pure HiBoot
      , pure Hi
      ]
  ]

-- | > <way prefix>_<o|hi|o-boot|hi-boot>
data Extension = Extension Way SuffixType deriving (Eq, Show)

parseExtension :: Parsec.Parsec String () Extension
parseExtension = Extension <$> parseWayPrefix vanilla <*> parseSuffixType

-- | > <file>.<way prefix>_<o|hi|o-boot|hi-boot>
data HsObject = HsObject Basename Extension deriving (Eq, Show)

parseHsObject :: Parsec.Parsec String () HsObject
parseHsObject = do
    file <- parseBasename
    ext <- parseExtension
    return (HsObject file ext)

data Object = Hs HsObject | NonHs NonHsObject deriving (Eq, Show)

parseObject :: Parsec.Parsec String () Object
parseObject = Parsec.choice
    [ NonHs <$> parseNonHsObject
    , Hs    <$> parseHsObject ]

-- * Toplevel parsers

parseBuildObject :: FilePath -> Parsec.Parsec String () (BuildPath Object)
parseBuildObject root = parseBuildPath root parseObject

-- * Getting contexts from objects

objectContext :: BuildPath Object -> Context
objectContext (BuildPath _ stage pkgPath obj) =
    Context stage (unsafeFindPackageByPath pkgPath) way Inplace
  where
    way = case obj of
        NonHs (NonHsObject _lang _file w)         -> w
        Hs    (HsObject _file (Extension w _suf)) -> w

-- * Building an object

compileHsObjectAndHi
    :: (FilePath -> Action (Maybe (String, [String])))
    -> [(Resource, Int)] -> FilePath -> Action ()
compileHsObjectAndHi readReceipt rs objpath = do
  root <- buildRoot
  b@(BuildPath _root stage _path _o)
    <- parsePath (parseBuildObject root) "<object file path parser>" objpath
  let ctx = objectContext b
      way = C.way ctx
  ctxPath <- contextPath ctx
  let depFile = ctxPath -/- ".dependencies"
      directory = root -/- "stage1/compiler/build"
  (src, deps) <- lookupDependencies depFile objpath
  let compileTarget = target ctx (Ghc CompileHs stage) [src] [objpath]
  selected <- if stage == Stage1 && C.package ctx == compiler && way == vanilla
                     && takeExtension objpath == ".o" && takeExtension src == ".hs"
              then orderOnlyAction $ do
                mode <- getEnv "HADRIAN_NORMALIZED_IFACE_WORKER"
                case mode of
                  Just _ -> Builder.builderPath (Ghc CompileHs stage) >>= Builder.normalizedIfaceWorker
                  Nothing -> pure Nothing
              else pure Nothing
  setup <- forM selected $ \helper@(_, _, digest) -> do
      providers <- orderOnlyAction (askOracle (HighFanout (depFile, directory)))
      let candidates = filter (`Set.member` providers) deps
      args <- if null candidates then pure [] else interpret compileTarget getArgs
      ready <- if "-dynamic-too" `notElem` args then pure [] else fmap catMaybes $
        forM candidates $ \provider -> do
          let stamp = provider -<.> "normalized-import"
          receipt <- orderOnlyAction (readReceipt stamp)
          pure $ case receipt of
            Just (tag, record) | tag == "helper-v1 " ++ digest -> Just (provider, stamp, record)
            _ -> Nothing
      pure (helper, args, ready)
  let potential = maybe [] (\(_, _, ready) -> [p | (p, _, _) <- ready]) setup
  need (src : filter (`notElem` potential) deps)
  orderOnly potential
  -- The .conf file is needed when template-haskell is implicitly added as a dependency
  -- when a module in the template-haskell package is compiled. (See #24737)
  when  (isLibrary (C.package ctx)) (need . (:[]) =<< pkgConfFile ctx)

  -- The .dependencies file lists indicating inputs. ghc will
  -- generally read more *.hi and *.hi-boot files (direct inputs).
  -- Allow such reads (see https://gitlab.haskell.org/ghc/ghc/wikis/Developing-Hadrian#haskell-object-files-and-hi-inputs)
  -- Note that this may allow too many *.hi and *.hi-boot files, but
  -- calculating the exact set of direct inputs is not feasible.
  trackAllow [ "**/*." ++ hisuf     way
             , "**/*." ++ hibootsuf way
             ]

  buildWithResources rs compileTarget
  forM_ setup $ \((daemon, libdir, _), args, ready) -> unless (null ready) $ do
    let ownHi = objpath -<.> "hi"
        ownDyn = objpath -<.> "dyn_hi"
    trackAllow [ownHi, ownDyn]
    cpp <- liftIO (hasCppPragmaPrefix src)
    certificate <- if cpp
      then pure Nothing
      else parseConsumer <$> Builder.ifaceWorkerQuery daemon
        (["certify", "--evidence", libdir, src, ownHi, ownDyn, "--"] ++ args ++ [src])
    case certificate of
      Nothing -> need potential
      Just uses -> forM_ ready $ \(provider, stamp, record) -> do
        if matchesProvider uses record
          then do
            need [stamp]
            putVerbose $ "normalized import " ++ objpath ++ " <- " ++ provider
          else need [provider]

compileNonHsObject :: [(Resource, Int)] -> SourceLang -> FilePath -> Action ()
compileNonHsObject rs lang path = do
  root <- buildRoot
  b@(BuildPath _root stage _path _o)
    <- parsePath (parseBuildObject root) "<object file path parser>" path
  let
    ctx = objectContext b
    builder = case lang of
      C -> Ghc CompileCWithGhc
      Cxx-> Ghc CompileCppWithGhc
      _ -> Ghc CompileHs
  src <- case lang of
      Asm -> obj2src "S"   (const False)      ctx path
      C   -> obj2src "c"   (const False)      ctx path
      Cmm -> obj2src "cmm" isGeneratedCmmFile ctx path
      Cxx -> obj2src "cpp" (const False) ctx path
      JS  -> obj2src "js" (const False) ctx path
  need [src]
  needDependencies lang ctx src (path <.> "d")
  buildWithResources rs $ target ctx (builder stage) [src] [path]

-- * Helpers

-- | Discover dependencies of a given source file by iteratively calling @gcc@
-- in the @-MM -MG@ mode and building generated dependencies if they are missing
-- until reaching a fixed point.
needDependencies :: SourceLang -> Context -> FilePath -> FilePath -> Action ()
needDependencies lang context@Context {..} src depFile = do
    gens <- interpretInContext context generatedDependencies
    need gens
    discover
  where
    discover = do
        build $ target context (Cc (FindCDependencies depType) stage) [src] [depFile]
        deps <- parseFile depFile
        -- Generated dependencies, if not yet built, will not be found and hence
        -- will be referred to simply by their file names.
        let notFound = filter (\file -> file == takeFileName file) deps
        -- We find the full paths to generated dependencies, so we can request
        -- to build them by calling 'need'.
        todo <- catMaybes <$> mapM (fullPathIfGenerated context) notFound

        if null todo
        then need deps -- The list of dependencies is final, need all
        else do
            need todo  -- Build newly discovered generated dependencies
            discover   -- Continue the discovery process

    -- We need to pass different flags to cc depending on whether the
    -- file to compile is a .c or a .cpp or a .S file
    depType = case lang of
                Cxx -> CxxDep
                Asm -> AsmDep
                _   -> CDep

    parseFile :: FilePath -> Action [String]
    parseFile file = do
        input <- liftIO $ readFile file
        case parseMakefile input of
            [(_file, deps)] -> return deps
            _               -> return []

-- | Find a given 'FilePath' in the list of generated files in the given
-- 'Context' and return its full path.
fullPathIfGenerated :: Context -> FilePath -> Action (Maybe FilePath)
fullPathIfGenerated context file = interpretInContext context $ do
    generated <- generatedDependencies
    return $ find ((== file) . takeFileName) generated

obj2src :: String -> (FilePath -> Bool) -> Context -> FilePath -> Action FilePath
obj2src extension isGenerated context@Context {..} obj
    | isGenerated src = return src
    | otherwise       = (pkgPath package ++) <$> suffix
  where
    src    = obj -<.> extension
    suffix = do
        path <- buildPath context
        return $ fromMaybe ("Cannot determine source for " ++ obj)
               $ stripPrefix (path -/- extension) src
