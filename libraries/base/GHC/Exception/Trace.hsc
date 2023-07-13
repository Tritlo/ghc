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
import Data.List ( intercalate, elemIndex, nub, intersect, sortOn, lookup)
import Data.Either (partitionEithers, rights)

#include "Rts.h"
foreign import ccall unsafe hs_hpc_rootModule :: IO (Ptr ())


-- | Returns the current HPC trace, with the module name, tix hash, next trace
-- index and the trace itself (the ints refer to boxes in the .mix file).
-- Reimplemented from libraries/hpc/Trace/Hpc/Reflect.hsc, to avoid a
-- circular dependency on trace from base.
traceList :: IO [([Char], Int, (Int,Int), ([Int], [Int], [Int]))]
traceList = hs_hpc_rootModule >>= hpcTraceList
  where
    hpcTraceList :: Ptr () -> IO [([Char], Int, (Int,Int), ([Int], [Int], [Int]))]
    hpcTraceList ptr
      | ptr == nullPtr = return []
      | otherwise = do
              modName <- ((#peek HpcModuleInfo, modName) ptr) >>= peekCString
              trxInfo :: Ptr Word64 <- (#peek HpcModuleInfo, trxInfo) ptr
              hashNo :: Int  <- (#peek HpcModuleInfo, hashNo) ptr
              info :: [Word64]  <- peekArray 3 trxInfo
              trxArr :: Ptr Word64 <- (#peek HpcModuleInfo, trxArr) ptr
              evalArr :: Ptr Word64 <- (#peek HpcModuleInfo, evaltrxArr) ptr
              gblArr :: Ptr Word64 <- (#peek HpcModuleInfo, gbltrxArr) ptr
              trx <- map fromIntegral <$> (peekArray (fromIntegral (info !! 2)) trxArr)
              eval <- map fromIntegral <$> (peekArray (fromIntegral (info !! 2)) evalArr)
              gbl <- map fromIntegral <$> (peekArray (fromIntegral (info !! 2)) gblArr)
              rest <- ((#peek HpcModuleInfo, next) ptr) >>= hpcTraceList
              return $ (modName, hashNo,
                        (fromIntegral (info !! 0),
                         fromIntegral (info !! 1)),
                        (trx,eval,gbl)) : rest



-- | Returns a summary of the current HPC trace if the .mix file is available,
-- showing which branches and functions have been recently evaluated.
traceMsgs :: IO [[Char]]
traceMsgs =
  do traces <- traceList
     dir <- maybe ".hpc/" id <$> lookupEnv "HPCDIR"
     let many_traces = length traces > 1

         -- readFiles :: [[Char]] -> IO (Map [Char] [[Char]])
         -- readFiles [] = Map.empty
         -- readLoc :: [Char] -> Map [Char] [[Char]] -> HpcPos -> [Char]
         -- readLoc file (P ls cs le ce) = 
            

         collect :: [ParseResult] -> ([ ([Char], [Char], (HpcPos,BaseBoxLabel))],
                                      [ ([Char], [Char], (HpcPos,BaseBoxLabel))])
         collect prs = collect' [] [] prs
            where collect' :: [(Int, [Char], [Char], (HpcPos,BaseBoxLabel))]
                           -> [(Int, [Char], [Char], (HpcPos,BaseBoxLabel))]
                           -> [ParseResult]
                           -> ([([Char], [Char], (HpcPos,BaseBoxLabel))],
                               [([Char], [Char], (HpcPos,BaseBoxLabel))]) 
                  collect' invs rests [] = (f invs, f rests)
                    where f = map (\(_,fn,m,e) -> (fn, m, e)) . sortOn (\(g,_,_,_) -> g) 
                  collect' invs rests ((PR{pr_filename=fn,pr_module=m,
                                           pr_inv_evals = inv_evals,
                                           pr_rest_evals = rest_evals}):prs)
                    = collect' (ni ++ invs) (nr ++ rests) prs
                        where ni = map f inv_evals
                              nr = map f rest_evals
                              f (e,g) = (g, fn, m, e)





     results <- mapM (parseAndReport many_traces dir) traces

     let (g_inv_evals, g_rest_evals) = collect $ rights results
         files = nub $ map (\(fn,_,_) -> fn) $
            g_inv_evals ++ g_rest_evals

     all_mods <- (zip files . map lines) <$> mapM readFile files
         
     let renderPos :: [Char] -> HpcPos -> ([Char], Bool)
         renderPos fn (P ls cs le ce) =
            case lookup fn all_mods of
                Nothing -> error $ "file not found " ++ fn
                Just (contents :: [[Char]]) -> 
                    let (first_line:i_lines) = if ls == le
                                               then [contents !! (ls -1)]
                                               else take ((le-ls)+1) $ drop (ls -1) contents
                        first_line' = drop (cs - 1) first_line
                        (last_line:r_lines) = reverse (first_line':i_lines)
                        last_line' = take (if ls == le
                                           then (ce - cs) +1
                                           else ce) last_line

                        referred = reverse (last_line':r_lines)
                    in (head referred, length last_line == length last_line')
                                      
         renderBB :: [Char] -> [Char] -> HpcPos -> BaseBoxLabel -> [Char]
         renderBB fn m p bb | TopLevelBox lbs <- bb = m ++ ":" ++ rtlbs lbs
                            | LocalBox (tl:lbs) <- bb = m ++ ":" ++ (wrap tl) ++ ">" ++ rtlbs lbs
                            | ExpBox True <- bb = "... = " ++ rendered
                            | ExpBox False <- bb = rendered
                            | BinBox CondBinBox True <- bb   = "... then " ++ rendered
                            | BinBox CondBinBox False <- bb  = "... else " ++ rendered
                            -- A GuardBinBox comes from a guard guards, i.e.
                            -- in | <condition> = ..., rendered will be condition
                            | BinBox GuardBinBox True <- bb  = "|...," ++ rendered ++ ",...=... (was matched)"
                            | BinBox GuardBinBox False <- bb = "|...," ++ rendered ++ ",...=... (not matched)"
                            -- These come from lists, i.e. in [ n | n <- [1..], <condition>] where 
                            -- condition is something like `even n`.
                            | BinBox QualBinBox True <- bb   = "[...|..., " ++ rendered ++ ",...] (was matched)"
                            | BinBox QualBinBox False <- bb  = "[...|..., " ++ rendered ++ ",...] (not matched)"
           where (rendered_base, was_eol) = renderPos fn p
                 qual_dots = if was_eol then "]" else ", ...]"
                 rendered = if length rendered_base >= 28
                            then (take 25 rendered_base) ++ "..."
                            else rendered_base
                 rtlbs lbs = intercalate ":" $ map wrap lbs
                 wrap :: [Char] -> [Char]
                 wrap s | (s1:_) <- s, isAlpha s1,
                          not (any isSpace s) = s
                        | otherwise = "(" ++ s ++ ")"
         rm_g :: (((HpcPos, BaseBoxLabel),Int),Int) -> 
                 ((HpcPos, BaseBoxLabel),Int)
         rm_g ((b,g),r) = (b,r)
         display :: [Char]
                 -> [Char]
                 -> Bool 
                 -> ((HpcPos, BaseBoxLabel),Int)
                 -> Maybe ([Char], [Char])
         display _ _ True ((_, ExpBox False),_) = Nothing
         display fn m _ ((p,bb),r) =
            Just ((replicate r ' ') ++ fn ++ ":" ++ show p, renderBB fn m p bb)



         disp_g b (fn, m, pb) = display fn m b (pb,0)
         g_res = summarize (align g_alt_disps)
                    ++ if null g_rev_disp then []
                    else ["Previous expressions:"] 
                        ++ (map (\s -> "  " ++ s) $ summarize (align g_rev_disp))
         (g_nonAlts,g_mbAlts) =
            span (not . isJust . disp_g True ) $
                reverse $ g_inv_evals
         g_alt_disps = mapMaybe (disp_g False) g_nonAlts 
                    ++ mapMaybe (disp_g True) g_mbAlts
         g_rev_disp = mapMaybe (disp_g True) $ reverse $ g_rest_evals

         -- TODO: do we want to split up per module?
         show_per_module = False
         global_trace = if many_traces || (not show_per_module)
                        then g_res
                        else []

         modOut :: Either [[Char]] ParseResult -> [[Char]]
         modOut (Left strs) = strs
         modOut (Right (PR {pr_filename=fn, pr_module=m, 
                            pr_inv_evals=inv_evals, pr_rest_evals=rest_evals})) =
            if many_traces
            then if null res then []
                 else pre ++ res
            else res

           where m_msg = "in module " ++ m ++ ":"
                 lns = replicate (length m_msg) '-'
                 pre = [lns, m_msg, lns]
                 res = summarize (align alt_disps)
                        ++ if null rev_disp then []
                        else ["Previous expressions:"] 
                            ++ (map (\s -> "  " ++ s) $ summarize (align rev_disp))
                    -- We want to display non-alternative exprs up until
                        -- the first branching one, and only branching afterwards
                 (nonAlts,mbAlts) = span (not . isJust . display fn m True . rm_g) $
                                     reverse $ zip inv_evals (repeat 0)
                 
                 alt_disps = mapMaybe (display fn m False . rm_g) nonAlts 
                          ++ mapMaybe (display fn m True . rm_g) mbAlts
                 rev_disp = mapMaybe (display fn m True . rm_g) $ 
                              reverse $ zip rest_evals (repeat 0)
     return $ global_trace ++ (if show_per_module
                               then ["","Per Module:"] ++ (concat $ map modOut results)
                               else [])
     

  where flip (a,b) = (b,a)
        align :: [([Char], [Char])] -> [[Char]]
        align strs = map c strs
          where longest :: Int
                longest = maximum (map (length . fst) strs)
                al :: [Char] -> [Char]
                al st = st ++ replicate ((longest - length st) + 1) ' '
                c :: ([Char], [Char]) -> [Char]
                c (s,[]) = s
                c (s,rd) = al s ++ " " ++ rd

       


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


data ParseResult = PR {pr_filename :: String, -- Name of the file 
                       pr_module :: String, -- Name of the module
                       pr_inv_evals :: [((HpcPos,BaseBoxLabel),Int)],
                        -- the evaluations up to the final evaluation depth in
                        -- reverse order, given as
                       pr_rest_evals :: [((HpcPos,BaseBoxLabel), Int)],
                        -- the evaluations after the final eval depth
                        -- in reverse order, given as the
                        -- (global order, index into pr_li)
                       pr_indented :: [(((HpcPos,BaseBoxLabel),Int),Int)], 
                       -- pr_indented is all the entries and the corresponding
                       -- evaluation depth together. Used to print the
                       -- the "eval snake"
                       pr_final_terminals :: [((HpcPos,BaseBoxLabel), Int)]
                       -- Terminals are values that immediately returned.
                       }


-- Report generation for traceMsg
parseAndReport :: Bool -> FilePath -> ([Char],Int,(Int,Int), ([Int],[Int],[Int]))
            -> IO (Either [[Char]] ParseResult)
parseAndReport more_than_1 dir (m, hash, (next_trx_index, final_evals), (trx, eval,gbl)) = do
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
           then Left ["** Error: Mixfile hash mismatch **", "File: " ++ hashstr,
                 "Module: " ++ show hash, "Try deleting: " ++ mixLoc]
           else case p_res of
                  Just p_li ->
                    let 
                        both_sides =  filter ((< (length p_li)) . fst . fst) $
                                        rot next_trx_index $
                                        zip (zip trx gbl) eval
                        -- We find the evals and the unevals,
                        -- and also decrease the indent by 1 for the unevals
                        -- to make the printing prettier.
                        unevals :: [((Int, Int),Int)] -> [(Int, Int)] -> [Either (Int, Int) (Int,Int)]
                                -> [((Int,Int),Int)] -> ([((Int,Int), Int)], [(Int,Int)], [Either (Int, Int) (Int,Int)])
                        unevals w_indent terms bth [(n,r)] =
                            if r > final_evals
                             then unevals ((n,r-1):w_indent) terms (Right n:bth) []
                             else unevals   ((n,r):w_indent) terms (Left  n:bth) []
                        unevals w_indent terms bth ((n,rn):k@(m,rm):rest)
                           = if rn > rm
                             then unevals ((n,rn-1):w_indent) terms (Right n:bth) (k:rest)
                             else if fst n ==  fst m
                                  -- If we see two in a row we just drop it,
                                  -- it finished right away. TODO: is this ok,
                                  -- when a recursive function calls itself
                                  -- immediately?
                                  then unevals            w_indent  (n:terms) (Left n:bth) (k:rest)
                                  else unevals    ((n,rn):w_indent)    terms  (Left n:bth) (k:rest)
                        unevals w_indent terms bth [] =
                           (reverse w_indent, reverse terms, reverse bth)
                        (indented, terms, evals_and_fins) =
                          unevals [] [] [] both_sides

                        -- Take while but keep the matching value
                        spanUntil f xs = case span f xs of
                                          (as, b:bs) -> (as ++ [b], bs)
                                          (as,bs) -> (as, bs)

                        -- We don't show unless they're within the current
                        -- evaluation depth
                        (inv_evals', rest_evals') =
                          spanUntil (\(_,i) -> i >= final_evals) $
                          reverse $ fst $ partitionEithers $
                          zipWith (\ef i -> case ef of
                                            Left x -> Left (x,i)
                                            Right x -> Right (x,i))
                                 evals_and_fins $ map snd both_sides

                        inv_evals  = map fst $ reverse inv_evals'
                        rest_evals = map fst $ reverse rest_evals'

                        -- Are the terminals useful?
                        final_terminals = (nub terms) `intersect` inv_evals

                        finalize = map (\(i,g) -> (p_li !! i, g)) 


                    in  Right (PR {pr_filename = fn,
                                   pr_module = m,
                                   pr_inv_evals = finalize inv_evals,
                                   pr_rest_evals = finalize rest_evals,
                                   pr_indented = map (\((i,g),r) -> ((p_li !! i, g),r)) indented,
                                   pr_final_terminals = finalize final_terminals })
                                         
                  Nothing -> Left ["** Error: could not parse Mix file" ++ mixLoc ++ " **"]
      Just _ -> Left ["** Error: Mix file " ++ mixLoc ++ " could not be read **"]
      Nothing -> Left ["** Error: Could not find .mix file for " ++ m ++ " **",
                      "Try setting $HPCDIR (with trailing slash)"]
    where parseMix :: [Char] -> Maybe [(HpcPos,BaseBoxLabel)]
          parseMix = readMaybe @[(HpcPos,BaseBoxLabel)]
          rot :: Int -> [a] -> [a]
          rot n xs = (drop n xs) ++ (take n xs)
          -- takes a paramter whether to ignore false ExpBoxes or not.

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

