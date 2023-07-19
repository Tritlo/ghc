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


data CollectResult = CR {cr_g :: Int, -- global index of this result
                         cr_i :: Int, -- the index in the mix file of is expr
                         cr_fe :: Int, -- the final eval depth in this module
                         cr_fn :: [Char], -- Filename of this expr
                         cr_m :: [Char], -- module name of the expr
                         cr_e :: (HpcPos, BaseBoxLabel), -- the expr
                         cr_r :: Int } -- eval depth of this expr


-- | Returns a summary of the current HPC trace if the .mix file is available,
-- showing which branches and functions have been recently evaluated.
traceMsgs :: IO [[Char]]
traceMsgs =
  do traces <- traceList
     dir <- maybe ".hpc/" id <$> lookupEnv "HPCDIR"

     let many_traces = length traces > 1
     results <- mapM (parseAndReport many_traces dir) traces

     let (gess,gefs) = collect $ rights results
         g_evals = reverse $ sortOn (cr_g) $ gess ++ gefs
         files = nub $ map cr_fn $ g_evals

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
                    in (head referred, ls == le)
         renderBB :: [Char] -> [Char] -> HpcPos -> BaseBoxLabel -> [Char]
         renderBB fn m p bb
            | TopLevelBox lbs <- bb = m ++ ":" ++ rtlbs lbs
            | LocalBox (tl:lbs) <- bb = m ++ ":" ++ (wrap tl) ++ ">" ++ rtlbs lbs
            -- ExpBoxes are expressions. If c is true, it is the result of
            -- a pattern match.
            | ExpBox c <- bb = (if c then "... = " else []) ++ rendered
            | BinBox CondBinBox c <- bb =
                "..." ++ (if c then "then" else "else") ++ " " ++ rendered
            -- A GuardBinBox comes from a guard guards, i.e.
            -- in | <condition> = ..., rendered will be condition
            | BinBox GuardBinBox c <- bb =
                "|...," ++ rendered ++ ",...=... " ++ show_mtch c
            -- These come from lists, i.e. in [ n | n <- [1..], <condition>] where
            -- condition is something like `even n`.
            | BinBox QualBinBox c <- bb =
                "[...|..., " ++ rendered ++ ",...] " ++ show_mtch c
           where (rendered_base, was_one_line) = renderPos fn p
                 rendered = if length rendered_base >= 28
                            then (take 25 rendered_base) ++ "..."
                            else rendered_base ++ (if was_one_line then [] else "...")
                 rtlbs lbs = intercalate ":" $ map wrap lbs
                 show_mtch True  = "(was matched)"
                 show_mtch False = "(not matched)"
                 wrap :: [Char] -> [Char]
                 wrap s | (s1:_) <- s, isAlpha s1,
                          not (any isSpace s) = s
                        | otherwise = "(" ++ s ++ ")"
         display :: [Char] -> [Char] -> Bool -> ((HpcPos, BaseBoxLabel),Int)
                 -> Maybe ([Char], [Char])
         display _ _ True ((_, ExpBox False),_) = Nothing
         display fn m _ ((p,bb),r) =
            Just ((replicate r ' ') ++ fn ++ ":" ++ show p, renderBB fn m p bb)

         g_final_eval = case g_evals of
                            (CR{cr_fe=fe}:_) -> fe
                            _ -> 0
         g_eval_starts = starts g_evals
          where starts [] = []
                starts [(n@CR{cr_r=rn})]
                    | rn > g_final_eval = []
                    | otherwise = [n]
                starts ((n@CR{cr_r=rn}):(m@CR{cr_r=rm}):rs)
                    | rn > rm = n:(starts (m:rs))
                    | otherwise = starts (m:rs)
         (g_evals_in_lvl, g_evals_rest) =
            spanUntil (\c -> (cr_r c) > g_final_eval) $ g_eval_starts

         disp_g b (CR{cr_g=g, cr_i=i, cr_fn=fn,
                      cr_m=m, cr_e=pb,cr_r=r}) = (\(l,c) ->(
                                        -- TODO: add debug flag here?
                                        -- show (g,i,r) ++ " " ++ show g_final_eval ++ " " ++
                                        l,c))
                                     <$> display fn m b (pb,0)
         g_res = summarize (align g_alt_disps)
                    ++ if null g_rev_disp then []
                    else ["Previous expressions:"] 
                        ++ (map (\s -> "  " ++ s) $ summarize (align g_rev_disp))
         (g_nonAlts,g_mbAlts) =
            span (not . isJust . disp_g True ) $ g_evals_in_lvl
         g_alt_disps = mapMaybe (disp_g False) g_nonAlts 
                    ++ mapMaybe (disp_g True) g_mbAlts
         g_rev_disp = mapMaybe (disp_g True) g_evals_rest
         -- g_rev_disp = mapMaybe (disp_g False) g_evals_rest
         -- TODO: make this a flag!
         show_per_module = False
         global_trace = if many_traces || (not show_per_module)
                        then g_res else []
         modOut :: Either [[Char]] ParseResult -> [[Char]]
         modOut (Left strs) = strs
         modOut (Right (PR {pr_filename=fn, pr_module=m, 
                            pr_eval_starts=eval_starts,
                            pr_eval_fins=eval_fins,
                            pr_final_eval_lvl=pr_final_eval
                            })) =
            if many_traces
            then if null res then [] else pre ++ res
            else res

           where m_msg = "in module " ++ m ++ ":"
                 lns = replicate (length m_msg) '-'
                 -- TODO: this might need fixing
                 (inv_evals',rest_evals') =
                    spanUntil (\(_,i) -> i >= pr_final_eval) $
                    reverse $ eval_starts
                 inv_evals = reverse inv_evals'
                 rest_evals = reverse rest_evals'
                 pre = [lns, m_msg, lns]
                 res = summarize (align alt_disps)
                        ++ if null rev_disp then []
                        else ["Previous expressions:"] 
                            ++ (map (\s -> "  " ++ s) $ summarize (align rev_disp))
                    -- We want to display non-alternative exprs up until
                        -- the first branching one, and only branching afterwards
                 (nonAlts,mbAlts) = span (not . isJust . display fn m True . rm_g) $
                                     reverse $ zip (map fst inv_evals) (repeat 0)
                 
                 alt_disps = mapMaybe (display fn m False . rm_g) nonAlts 
                          ++ mapMaybe (display fn m True . rm_g) mbAlts
                 rev_disp = mapMaybe (display fn m True . rm_g) $ 
                              reverse $ zip (map fst rest_evals) (repeat 0)
                 rm_g :: ((Int,(HpcPos, BaseBoxLabel),Int),Int) ->
                            ((HpcPos, BaseBoxLabel),Int)
                 rm_g ((i,b,g),r) = (b,r)
     return $ global_trace ++
                (if show_per_module
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
                       pr_final_eval_lvl :: Int, -- The final eval depth
                       -- (expression, global_trace_index, eval_depth)
                       pr_eval_starts :: [((Int, (HpcPos,BaseBoxLabel),Int), Int)],
                        -- the evaluations up to the final evaluation depth in
                       pr_eval_fins :: [((Int, (HpcPos,BaseBoxLabel), Int), Int)],
                        -- the evaluations after the final eval depth
                        -- in reverse order, given as the
                        -- (global order, index into pr_li)
                       pr_indented :: [((Int, (HpcPos,BaseBoxLabel),Int),Int)],
                       -- pr_indented is all the entries and the corresponding
                       -- evaluation depth together. Used to print the
                       -- the "eval snake"
                       pr_final_terminals :: [(Int,(HpcPos,BaseBoxLabel), Int)]
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
                        unevals w_indent terms bth [(n@(gn,vn),r)] =
                            -- TODO: This might not be the right thing to do
                            -- for global evals.
                            if r > final_evals
                             then unevals ((n,r-1):w_indent) terms (Right n:bth) []
                             else unevals   ((n,r):w_indent) terms (Left  n:bth) []
                        unevals w_indent terms bth ((n@(vn,gn),rn):k@(m@(vm,gm),rm):rest)
                           = if rn > rm
                             then unevals ((n,rn-1):w_indent) terms (Right n:bth) (k:rest)
                             else if vn ==  vm
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


                        -- We don't show unless they're within the current
                        -- evaluation depth
                        (eval_starts, eval_fins) =
                          -- spanUntil (\(_,i) -> i >= final_evals) $
                          -- reverse $ fst $
                          partitionEithers $
                          zipWith (\ef i -> case ef of
                                            Left x -> Left (x,i)
                                            Right x -> Right (x,i))
                                 evals_and_fins $ map snd both_sides


                        -- Are the terminals useful?
                        final_terminals = (nub terms) `intersect` 
                                            (map fst eval_starts)

                        finalize = map (\((i,g),r) -> ((i,p_li !! i, g), r))


                    in  Right (PR {pr_filename = fn,
                                   pr_module = m,
                                   pr_final_eval_lvl = final_evals,
                                   pr_eval_starts = finalize eval_starts,
                                   pr_eval_fins = finalize eval_fins,
                                   pr_indented = finalize indented,
                                   pr_final_terminals = 
                                    map (\(i,g) -> (i,p_li !! i,g)) final_terminals })
                                         
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

-- Take while but keep the matching value
spanUntil f xs = case span f xs of
                    (as, b:bs) -> (as ++ [b], bs)
                    (as,bs) -> (as, bs)

collect :: [ParseResult] -> ([CollectResult], [CollectResult])
collect prs = collect' [] [] prs
   where collect' :: [CollectResult] -> [CollectResult]
                  -> [ParseResult]
                  -> ([CollectResult], [CollectResult])
         collect' invs rests [] = (invs, rests)
         collect' invs rests ((PR{pr_filename=fn,pr_module=m,
                                  pr_eval_starts = eval_starts,
                                  pr_eval_fins = eval_fins,
                                  pr_final_eval_lvl = prfe
                                  }):prs)
           = collect' (ni ++ invs) (nr ++ rests) prs
               where ni = map f eval_starts
                     nr = map f eval_fins
                     f ((i,e,g),r) = CR{cr_g=g, cr_i=i, cr_fe=prfe,
                                        cr_fn=fn, cr_m=m, cr_e=e,
                                        cr_r=r}
