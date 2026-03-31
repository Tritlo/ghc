{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module GHC.Internal.Exception.Trace ( traceList, traceMsgs ) where

import GHC.Internal.Base ( String,
                           (.), ($), (++), (>>), (>>=),
                           otherwise, return, map, id, const, mapM )
import GHC.Internal.Types ( Bool(..), Char, Int, IO )
import GHC.Internal.IO ( FilePath )
import GHC.Internal.Maybe ( Maybe(..) )
import GHC.Internal.Classes ( Eq(..), Ord(..), not, (&&) )
import GHC.Internal.Num ( (+), (-) )
import GHC.Internal.Data.Functor ( (<$>) )
import GHC.Internal.Show ( Show(..) )
import GHC.Internal.Read ( Read(..) )
import GHC.Internal.Real ( fromIntegral )
import GHC.Internal.Data.Tuple ( fst )
import GHC.Internal.Err ( error )
import GHC.Internal.List ( filter, span, reverse, take, drop, splitAt, zip, concat, length, replicate, repeat, null, takeWhile, (!!), any, maximum )
import GHC.Internal.Foreign.C.String
import GHC.Internal.Foreign.Marshal.Array
import GHC.Internal.Foreign.Ptr
import GHC.Internal.Foreign.Storable ( Storable (..))
import GHC.Internal.Data.Maybe ( mapMaybe, isJust, maybe )
import GHC.Internal.Data.OldList ( intercalate, elemIndex )
import GHC.Internal.Word
import GHC.Internal.Text.Read ( readMaybe, read )
import GHC.Internal.System.IO ( readFile )
import GHC.Internal.System.Environment ( lookupEnv )
import GHC.Internal.Control.Exception ( catch )
import GHC.Internal.Unicode ( isAlpha, isSpace )
import GHC.Internal.IO.Exception ( IOException )

#include "Rts.h"
foreign import ccall unsafe hs_hpc_rootModule :: IO (Ptr ())


-- | Returns the current HPC trace...
traceList :: IO [([Char], Int, Int, [Int])]
traceList = hs_hpc_rootModule >>= hpcTraceList
  where
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

-- | Returns a summary of the current HPC trace...
traceMsgs :: IO [[Char]]
traceMsgs =
  do traces <- traceList
     dir <- maybe ".hpc/" id <$> lookupEnv "HPCDIR"
     concat <$> mapM (parseAndReport dir) traces


--- Mix parsing...
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

data BaseBoxLabel = ExpBox  Bool
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
      Just r | (header,_:rest) <- splitAt 4 r,
               header == "Mix ",
               (fn,_:_:wofn) <- span (/= '"') rest,
               (_, _:woutcdate) <- span (/= ' ') wofn,
               (_, _:woutctime) <- span (/= ' ') woutcdate,
               (_, _:woutcheader) <- span (/= ' ') woutctime,
               (hashstr, _:wohash) <- span (/= ' ') woutcheader,
               (_, _:mix_li) <- span (/= ' ') wohash,
               p_res <- parseMix mix_li ->
           if ((read hashstr) :: Word32) /= ((fromIntegral hash) :: Word32)
           then ["** Error: Mixfile hash mismatch **", "File: " ++ hashstr,
                 "Module: " ++ show hash, "Try deleting: " ++ mixLoc]
           else case p_res of
                  Just p_li ->
                    let look skipNonAlt i =
                           if i >= length p_li then Nothing
                           else (display skipNonAlt (fn, p_li !! i))
                        (nonAlts,mbAlts) = span (not . isJust . look True)
                                            $ filter (< (length p_li))
                                            $ reverse $ rot next_index trx
                    in summarize $ align $ mapMaybe (look False) nonAlts
                                        ++ mapMaybe (look True) mbAlts
                  Nothing -> ["** Error: could not parse Mix file" ++ mixLoc ++ " **"]
      Just _ -> ["** Error: Mix file " ++ mixLoc ++ " could not be read **"]
      Nothing -> ["** Error: Could not find .mix file for " ++ m ++ " **",
                  "Try setting $HPCDIR (with trailing slash)"]
    where parseMix :: [Char] -> Maybe [(HpcPos,BaseBoxLabel)]
          parseMix = readMaybe @[(HpcPos,BaseBoxLabel)]
          rot :: Int -> [a] -> [a]
          rot n xs = (drop n xs) ++ (take n xs)
          display :: Bool -> ([Char], (HpcPos, BaseBoxLabel)) -> Maybe ([Char], [Char])
          display True (_, (_, ExpBox False)) = Nothing
          display _ (fn, (p,bb)) = Just (fn ++ ":" ++ show p, renderBB bb)
          renderBB bb | TopLevelBox lbs <- bb = m ++ ":" ++ rtlbs lbs
                      | LocalBox (tl:lbs) <- bb = m ++ ":" ++ (wrap tl) ++ ">" ++ rtlbs lbs
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

summarize :: [[Char]] -> [[Char]]
summarize = mergeNRepeats 5
  where
    mergeNRepeats :: Int -> [[Char]] -> [[Char]]
    mergeNRepeats 0 i = i
    mergeNRepeats n i = mergeNRepeats (n-1) $ mergeRepeats i
    mergeRepeats :: [[Char]] -> [[Char]]
    mergeRepeats [] = []
    mergeRepeats inp@(loop_head:rest) =
      case elemIndex loop_head rest of
          Nothing -> keepGoing
          Just i ->
            let (whole_loop, new_rest) = splitAt (i+1) inp
                chunks = chunkList (i+1) new_rest
                (same,diff) = span (== whole_loop) chunks
            in if null same then keepGoing
               else let indent = length $ takeWhile (== ' ') loop_head
                        msg = replicate indent ' ' ++ "repeats ("
                               ++ show (1 + length same) ++ " times):"
                        indented = map ("  "++) whole_loop
                    in (msg:indented) ++ mergeRepeats (concat diff)
      where
          keepGoing = loop_head:mergeRepeats rest
          chunkList _ [] = []
          chunkList i xs = let (s,r) = splitAt i xs in s:chunkList i r
