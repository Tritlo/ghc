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
import Text.Read ( readMaybe )
import System.Environment
import Control.Exception
import Data.Maybe ( mapMaybe, isJust )
import Data.Char ( isAlpha, isSpace )
import Data.List ( intercalate, elemIndex )
import Data.Function (fix)

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


parseAndReport :: FilePath -> ([Char],Int,Int,[Int]) -> IO [[Char]]
parseAndReport dir (m, hash, next_index, trx) = do
    let mixLoc = dir ++ m ++ ".mix" 
    res <- catch @IOException
             (Just <$> readFile mixLoc)
             (\_ -> return Nothing)
    return $ case res of
      Nothing -> ["** Error: Could not find .mix file for " ++ m ++ " **",
                  "Try setting $HPCDIR (with trailing slash)"]
      Just r | (header,_) <- splitAt 4 r,
               header /= "Mix " -> ["** Error: Mix file is corrupted **"]
      Just r | rest <- drop 5 r -> 
        let (fn,_:_:wofn) = span (/= '"') rest
            (_, _:woutcdate)  = span (/= ' ') wofn -- utcdate
            (_, _:woutctime)  = span (/= ' ') woutcdate -- utctime
            (_, _:woutcheader) = span (/= ' ') woutctime -- utcheader
            (hashstr, _:wohash) = span (/= ' ') woutcheader
            (_, _:mix_li) = span (/= ' ') wohash -- lenstr
            p_res = parseMix mix_li
        in if ((read hashstr) :: Word32) /= ((fromIntegral hash) :: Word32)
           then ["** Error: Mixfile hash mismatch **",
                 "File: " ++ hashstr,
                 "Module: " ++ show hash,
                 "Try deleting: " ++ mixLoc]
           else case p_res of
                  Just p_li ->
                    let look skipNonAlt i =
                           if i < length p_li
                           then (display skipNonAlt (fn, p_li !! i))
                           else Nothing
                        -- We want to display non-alternative exprs
                        -- up until the first interesting one and then
                        -- just the interesting stuff from thereon.
                        (nonAlts,mbAlts) = span (not . isJust . look True)
                                            $ filter (< (length p_li))
                                            $ reverse $ rot next_index trx
                    in (align $ mapMaybe (look False) nonAlts
                             ++ mapMaybe (look True) mbAlts)
                  Nothing -> ["** Error: could not parse Mix file **"]
    where parseMix :: [Char] -> Maybe [(HpcPos,BaseBoxLabel)]
          parseMix = readMaybe @[(HpcPos,BaseBoxLabel)]
          display :: Bool -> ([Char], (HpcPos, BaseBoxLabel)) -> Maybe ([Char], [Char])
          display True (fn, (p, ExpBox False)) = Nothing
          display _ (fn, (p,bb)) = Just (fn ++ ":" ++ show p, renderBB bb)

          renderBB bb | TopLevelBox lbs <- bb =
                            m ++ ":" ++ rtlbs lbs
                      | LocalBox (tl:lbs) <- bb = 
                            m ++ ":" ++ (wrap tl) ++ ">" ++ rtlbs lbs
                      | LocalBox [] <- bb =  "empty local box?"
                      | ExpBox True <- bb = "alternative branch taken"
                      | ExpBox False <- bb = ""
                      | BinBox CondBinBox True <- bb   = "then branch taken"
                      | BinBox CondBinBox False <- bb  = "else branch taken"
                      | BinBox QualBinBox True <- bb   = "qualifying branch taken "
                      | BinBox QualBinBox False <- bb  = "qualifying branch not taken"
                      | BinBox GuardBinBox True <- bb  = "guarded branch taken"
                      | BinBox GuardBinBox False <- bb = "guarded branch not taken"
            where rtlbs lbs = intercalate ":" $ map wrap lbs
                  wrap :: [Char] -> [Char]
                  wrap s | (s1:_) <- s, isAlpha s1,
                           not (any isSpace s) = s
                         | otherwise = "(" ++ s ++ ")"
          align :: [([Char], [Char])] -> [[Char]]
          align strs = map c strs
            where longest :: Int
                  longest = maximum (map (length . fst) strs)
                  al :: [Char] -> [Char]
                  al st = st ++ replicate ((longest - length st) + 1) ' '
                  c :: ([Char], [Char]) -> [Char]
                  c (s,[]) = s
                  c (s,rd) = al s ++ rd


rot :: Int -> [a] -> [a]
rot n xs = (drop n xs) ++ (take n xs)

traceMsgs :: IO [[Char]]
traceMsgs = 
  do traces <- traceList
     dir <- maybe ".hpc/" id <$> lookupEnv "HPCDIR" 
     concat <$> mapM (parseAndReport dir) traces
