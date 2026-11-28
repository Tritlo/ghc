module Rules.Dependencies (buildPackageDependencies) where

import qualified Data.HashMap.Lazy as HashMap

import Base
import Context
import Expression
import Hadrian.BuildPath
import Oracles.ModuleFiles
import Rules.Generate
import Settings
import Target
import Utilities

import qualified Text.Parsec as Parsec

buildPackageDependencies :: [(Resource, Int)] -> Rules ()
buildPackageDependencies rs = do
    dependencyWorkerRules
    root <- buildRootRules
    root -/- "**/.dependencies.mk" %> \mk -> do
        DepMkFile stage pkgpath <- getDepMkFile root mk
        let pkg = unsafeFindPackageByPath pkgpath
            context = Context stage pkg vanilla Inplace
        srcs <- hsSources context
        gens <- interpretInContext context generatedDependencies
        need (srcs ++ gens)
        if null srcs
        then writeFileChanged mk ""
        else buildWithResources rs $ target context
            (Ghc FindHsDependencies $ Context.stage context) srcs [mk]
        removeFile $ mk <.> "bak"

    root -/- "**/.dependencies" %> \deps -> do
        mkDeps <- readFile' (deps <.> "mk")
        -- fromListWith (++) prepends each new row to the previous rows for
        -- its target. Reverse the input to preserve the prerequisite order.
        let byTarget = HashMap.fromListWith (++) (reverse (parseMakefile mkDeps))
        writeFileChanged deps $
            unlines
                [ unwords (map unifyPath (targetPath : prerequisites))
                | (targetPath, prerequisites) <- sortOn fst (HashMap.toList byTarget)
                ]


data DepMkFile = DepMkFile Stage FilePath deriving (Eq, Show)

parseDepMkFile :: FilePath -> Parsec.Parsec String () DepMkFile
parseDepMkFile root = do
    _ <- Parsec.string root *> Parsec.optional (Parsec.char '/')
    stage <- parseStage
    _ <- Parsec.char '/'
    pkgPath <- Parsec.manyTill Parsec.anyChar
        (Parsec.try $ Parsec.string "/.dependencies.mk")
    return (DepMkFile stage pkgPath)

getDepMkFile :: FilePath -> FilePath -> Action DepMkFile
getDepMkFile root = parsePath (parseDepMkFile root) "<dependencies file>"
