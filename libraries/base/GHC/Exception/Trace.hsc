{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module GHC.Exception.Trace ( traceList, traceMsgs ) where

import Foreign.C.String
import Foreign.Marshal.Array
import Foreign.Ptr
import Foreign.Storable ( Storable (..))
import Data.Word
import Text.Read
import System.Environment
import Control.Exception

#include "Rts.h"
foreign import ccall unsafe hs_hpc_rootModule :: IO (Ptr ())

-- HPC runtime trace. Reimplemented from libraries/hpc/Trace/Hpc/Reflect.hsc,
-- to avoid a circular dependency on trace from base.


traceList :: IO [([Char], Int, Int, [Int])]
traceList = hs_hpc_rootModule >>= hpcTraceList

hpcTraceList :: Ptr () -> IO [([Char], Int, Int, [Int])]
hpcTraceList ptr
  | ptr == nullPtr = return []
  | otherwise = do
        modName <- ((#peek HpcModuleInfo, modName) ptr) >>= peekCString
        trxInfo :: Ptr Word64 <- (#peek HpcModuleInfo, trxInfo) ptr
        hashNo :: Int  <- (#peek HpcModuleInfo, hashNo) ptr
        info :: [Word64]  <- peekArray 2 trxInfo
        trxArr :: Ptr Word64 <- (#peek HpcModuleInfo, trxArr) ptr
        trx <- map fromIntegral <$> (peekArray (fromIntegral (info !! 1)) trxArr)
        rest <- ((#peek HpcModuleInfo, next) ptr) >>= hpcTraceList
        return $ (modName, hashNo,
                  fromIntegral (info !! 0), trx) : rest



--- Mix parsing:
data HpcPos = P !Int !Int !Int !Int deriving (Eq, Ord)

toHpcPos :: (Int,Int,Int,Int) -> HpcPos
toHpcPos (l1,c1,l2,c2) = P l1 c1 l2 c2

instance Show HpcPos where
   show (P l1 c1 l2 c2) = show l1 ++ ':' : show c1 ++ '-' : show l2 ++ ':' : show c2

instance Read HpcPos where
  readsPrec _i pos = [(toHpcPos (read l1,read c1,read l2,read c2),after)]
      where
         (before,after) = span (/= ',') pos
         parseError a   = error $ "Read HpcPos: Could not parse: " ++ show a
         (lhs0,rhs0)    = case span (/= '-') before of
                               (lhs,'-':rhs) -> (lhs,rhs)
                               (lhs,"")      -> (lhs,lhs)
                               _ -> parseError before
         (l1,c1)        = case span (/= ':') lhs0 of
                            (l,':':c) -> (l,c)
                            _ -> parseError lhs0
         (l2,c2)        = case span (/= ':') rhs0 of
                            (l,':':c) -> (l,c)
                            _ -> parseError rhs0

data BaseBoxLabel = ExpBox  Bool -- isAlt
                  | TopLevelBox [String]
                  | LocalBox [String]
                  | BinBox BaseCondBox Bool
                   deriving (Read)

data BaseCondBox = GuardBinBox
                 | CondBinBox
                 | QualBinBox
                  deriving (Read)

parseMix :: String -> Maybe [HpcPos]
parseMix = fmap (map fst) . readMaybe @[(HpcPos,BaseBoxLabel)]

parseAndReport :: FilePath -> ([Char],Int,Int,[Int]) -> IO [[Char]]
parseAndReport dir (m, hash, next_index, trx) = do
    let mixLoc = dir ++ m ++ ".mix" 
    res <- catch @IOException
             (Just <$> readFile mixLoc)
             (\_ -> return Nothing)
    return $ case res of
      Nothing -> ["** Error: Could not find .mix file for " ++ m ++ "**",
                  "Try setting $HPCDIR (with trailing slash)"]
      Just r | (header,rest) <- splitAt 4 r,
               header /= "Mix " -> ["** Error: Mix file is corrupted **"]
      Just r | rest <- drop 5 r -> 
        let (fn,_:_:wofn) = span (/= '"') rest
            (utcdate, _:woutcdate)  = span (/= ' ') wofn
            (utctime, _:woutctime)  = span (/= ' ') woutcdate
            (utcheader, _:woutcheader) = span (/= ' ') woutctime
            (hashstr, _:wohash) = span (/= ' ') woutcheader
            (lenstr, _:mix_li) = span (/= ' ') wohash
            p_res = parseMix mix_li
        in if ((read hashstr) :: Word32) /= ((fromIntegral hash) :: Word32)
           then ["** Error: Mixfile hash mismatch **",
                 "File: " ++ hashstr,
                 "Module: " ++ show hash,
                 "Try deleting: " ++ mixLoc]
           else case p_res of
                  Just p_li ->
                    let look i = 
                           if i < length p_li
                           then (fn ++ ":" ++show (p_li !! i))
                           else "Index " ++ show i ++" too large, wrong .mix file?"
                    in (reverse $ rot next_index $ map look trx)
                  Nothing -> ["** Error: could not parse Mix file **"]

rot :: Int -> [a] -> [a]
rot n xs = (drop n xs) ++ (take n xs)

traceMsgs :: IO [[Char]]
traceMsgs = 
  do traces <- traceList
     dir <- maybe ".hpc/" id <$> lookupEnv "HPCDIR" 
     concat <$> mapM (parseAndReport dir) traces
