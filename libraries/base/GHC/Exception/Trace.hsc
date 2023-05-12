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
import Data.Either (partitionEithers)

#include "Rts.h"
foreign import ccall unsafe hs_hpc_rootModule :: IO (Ptr ())


-- | Returns the current HPC trace, with the module name, tix hash, next trace
-- index and the trace itself (the ints refer to boxes in the .mix file).
-- Reimplemented from libraries/hpc/Trace/Hpc/Reflect.hsc, to avoid a
-- circular dependency on trace from base.
traceList :: IO [([Char], Int, (Int,Int), ([Int], [Int]))]
traceList = hs_hpc_rootModule >>= hpcTraceList
  where
    hpcTraceList :: Ptr () -> IO [([Char], Int, (Int,Int), ([Int], [Int]))]
    hpcTraceList ptr
      | ptr == nullPtr = return []
      | otherwise = do
              modName <- ((#peek HpcModuleInfo, modName) ptr) >>= peekCString
              trxInfo :: Ptr Word64 <- (#peek HpcModuleInfo, trxInfo) ptr
              hashNo :: Int  <- (#peek HpcModuleInfo, hashNo) ptr
              info :: [Word64]  <- peekArray 3 trxInfo
              trxArr :: Ptr Word64 <- (#peek HpcModuleInfo, trxArr) ptr
              retArr :: Ptr Word64 <- (#peek HpcModuleInfo, rettrxArr) ptr
              trx <- map fromIntegral <$> (peekArray (fromIntegral (info !! 2)) trxArr)
              ret <- map fromIntegral <$> (peekArray (fromIntegral (info !! 2)) retArr)
              rest <- ((#peek HpcModuleInfo, next) ptr) >>= hpcTraceList
              return $ (modName, hashNo,
                        (fromIntegral (info !! 0),
                         fromIntegral (info !! 1)),
                        (trx,ret)) : rest

-- | Returns a summary of the current HPC trace if the .mix file is available,
-- showing which branches and functions have been recently evaluated.
traceMsgs :: IO [[Char]]
traceMsgs =
  do traces <- traceList
     dir <- maybe ".hpc/" id <$> lookupEnv "HPCDIR"
     concat <$> mapM (parseAndReport dir) traces


--- Mix parsing. Taken from libraries/hpc/Trace/Hpc/Mix.hs to avoid circular
-- dependencies.
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


-- Report generation for traceMsg
parseAndReport :: FilePath -> ([Char],Int,(Int,Int), ([Int],[Int])) -> IO [[Char]]
parseAndReport dir (m, hash, (next_trx_index, final_evals), (trx, ret)) = do
    let mixLoc = dir ++ m ++ ".mix"
    res <- catch @IOException
             (Just <$> readFile mixLoc)
             (\_ -> return Nothing)
    return $ case res of
      Just r | (header,_:rest) <- splitAt 4 r,
               header == "Mix ",
               (fn,_:_:wofn) <- span (/= '"') rest,
               (_, _:woutcdate) <- span (/= ' ') wofn, -- utcdate
               (_, _:woutctime) <- span (/= ' ') woutcdate, -- utctime
               (_, _:woutcheader) <- span (/= ' ') woutctime, -- utcheader
               (hashstr, _:wohash) <- span (/= ' ') woutcheader,
               (_, _:mix_li) <- span (/= ' ') wohash, -- lenstr
               p_res <- parseMix mix_li ->
           if ((read hashstr) :: Word32) /= ((fromIntegral hash) :: Word32)
           then ["** Error: Mixfile hash mismatch **", "File: " ++ hashstr,
                 "Module: " ++ show hash, "Try deleting: " ++ mixLoc]
           else case p_res of
                  Just p_li ->
                    let look skipNonAlt (i,r) =
                           if i >= length p_li then Nothing
                           else (display skipNonAlt (fn, i, r, p_li !! i))
                        -- We want to display non-alternative exprs up until
                        -- the first branching one, and only branching afterwards
                        both_sides =  filter ((< (length p_li)) . fst) $
                                        rot next_trx_index $ zip trx ret
                        -- We find the evals and the unevals,
                        -- and also decrease the indent by 1 for the unevals
                        -- to make the printing prettier.
                        unevals :: [(Int,Int)] -> [Either Int Int] -> [(Int,Int)]
                                -> ([(Int, Int)], [Either Int Int])
                        unevals w_indent bth [(n,r)] =
                            if r > final_evals
                             then unevals ((n,r-1):w_indent) (Left  n:bth) []
                             else unevals   ((n,r):w_indent) (Right n:bth) []
                        unevals w_indent bth ((n,rn):k@(m,rm):rest)
                           = if rn > rm
                             then unevals ((n,rn-1):w_indent)  (Left  n:bth) (k:rest)
                             else if n == m
                                  -- If we see two in a row we just drop it,
                                  -- it finished right away. TODO: is this ok,
                                  -- when a recursive function calls itself
                                  -- immediately?
                                  then unevals            w_indent   (Right n:bth) (k:rest)
                                  else unevals    ((n,rn):w_indent)  (Right n:bth) (k:rest)
                        unevals w_indent bth [] =
                           (reverse w_indent, reverse bth)
                        (indented, evals_and_fins) =
                          unevals [] [] $ both_sides
                        (evals, _) = partitionEithers evals_and_fins


                    -- in summarize (align $ mapMaybe (look False) nonAlts
                    --                     ++ mapMaybe (look True) mbAlts)
                    --    -- TODO: Improve
                    --    ++ ["Finished evaluating:"]
                    --    ++ summarize (align $ mapMaybe (look False) nonRetAlts
                    --                        ++ mapMaybe (look True) mbRetAlts)
                    -- in summarize (align $ mapMaybe (look False) $ zip alts ret_alts)
                    in  summarize (align $ mapMaybe (look True) $ zip evals (repeat 0))
                      ++ ["Eval snake:"]
                      ++ (align $ mapMaybe (look False) indented)
                  Nothing -> ["** Error: could not parse Mix file" ++ mixLoc ++ " **"]
      Just _ -> ["** Error: Mix file " ++ mixLoc ++ " could not be read **"]
      Nothing -> ["** Error: Could not find .mix file for " ++ m ++ " **",
                  "Try setting $HPCDIR (with trailing slash)"]
    where parseMix :: [Char] -> Maybe [(HpcPos,BaseBoxLabel)]
          parseMix = readMaybe @[(HpcPos,BaseBoxLabel)]
          rot :: Int -> [a] -> [a]
          rot n xs = (drop n xs) ++ (take n xs)
          -- takes a paramter whether to ignore false ExpBoxes or not.
          display :: Bool -> ([Char], Int, Int, (HpcPos, BaseBoxLabel)) -> Maybe ([Char], [Char])
          display True (_, _, _, (_, ExpBox False)) = Nothing
          display _ (fn, i, r, (p,bb)) =
            Just ( (replicate r ' ') ++ show i ++ " " ++ fn ++ ":" ++ show p, renderBB bb)
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

-- summarize is simplistic for now, and just detects repeats in the output.
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

