{-# OPTIONS_GHC -fno-warn-orphans #-} -- We don't want to spread the HasOccName
                                      -- instance for Either
module TcHoleErrors ( findValidHoleFits ) where

import GhcPrelude

import TcSimplify ( tcCheckHoleFit, tcSubsumes )


import TcRnTypes
import TcRnMonad
import TcMType
import TcEvidence
import TcType
import Type
import DataCon
import Name
import RdrName ( pprNameProvenance , GlobalRdrElt (..), globalRdrEnvElts )
import PrelNames ( gHC_ERR )
import Id
import VarSet
import VarEnv
import Bag
import ConLike          ( ConLike(..))
import Util
import TcEnv (tcLookup)
import Outputable
import DynFlags
import Maybes
import FV ( fvVarList, fvVarSet )

import Control.Monad    ( filterM, replicateM )
import Data.List        ( partition, sort, sortOn, nubBy, foldl' )
import Data.Graph       ( graphFromEdges, topSort )
import Data.Function    ( on )

-- SPJ
-- This is a super-important Note. Can you put it at the top of this module?
-- And review it carefully to make sure it really describes all the moving parts. Including the business about building an implication constraint, with an example or two to support it.

{-
Note [Valid hole fits include ...]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
`findValidHoleFits` returns the "Valid hole fits include ..." message.
For example, look at the following definitions in a file called test.hs:

   import Data.List (inits)

   f :: [String]
   f = _ "hello, world"

The hole in `f` would generate the message:

  • Found hole: _ :: [Char] -> [String]
  • In the expression: _
    In the expression: _ "hello, world"
    In an equation for ‘f’: f = _ "hello, world"
  • Relevant bindings include f :: [String] (bound at test.hs:6:1)
    Valid hole fits include
      lines :: String -> [String]
        (imported from ‘Prelude’ at mpt.hs:3:8-9
          (and originally defined in ‘base-4.11.0.0:Data.OldList’))
      words :: String -> [String]
        (imported from ‘Prelude’ at mpt.hs:3:8-9
          (and originally defined in ‘base-4.11.0.0:Data.OldList’))
      inits :: forall a. [a] -> [[a]]
        with inits @Char
        (imported from ‘Data.List’ at mpt.hs:4:19-23
          (and originally defined in ‘base-4.11.0.0:Data.OldList’))
      repeat :: forall a. a -> [a]
        with repeat @String
        (imported from ‘Prelude’ at mpt.hs:3:8-9
          (and originally defined in ‘GHC.List’))
      fail :: forall (m :: * -> *). Monad m => forall a. String -> m a
        with fail @[] @String
        (imported from ‘Prelude’ at mpt.hs:3:8-9
          (and originally defined in ‘GHC.Base’))
      return :: forall (m :: * -> *). Monad m => forall a. a -> m a
        with return @[] @String
        (imported from ‘Prelude’ at mpt.hs:3:8-9
          (and originally defined in ‘GHC.Base’))
      pure :: forall (f :: * -> *). Applicative f => forall a. a -> f a
        with pure @[] @String
        (imported from ‘Prelude’ at mpt.hs:3:8-9
          (and originally defined in ‘GHC.Base’))
      read :: forall a. Read a => String -> a
        with read @[String]
        (imported from ‘Prelude’ at mpt.hs:3:8-9
          (and originally defined in ‘Text.Read’))
      mempty :: forall a. Monoid a => a
        with mempty @([Char] -> [String])
        (imported from ‘Prelude’ at mpt.hs:3:8-9
          (and originally defined in ‘GHC.Base’))

Valid hole fits are found by checking top level identifiers in scope for
whether their type is subsumed by the type of the hole. Additionally, as
highlighted by Trac #14273, we also need to check whether all relevant
constraints are solved by choosing an identifier of that type as well. This is
to make sure we don't suggest a hole fit which does not fulfill the
constraints imposed on the hole (even though it has a type that would otherwise
fit the hole). The relevant constraints are those whose free unification
variables are all mentioned by the type of the hole. Since checking for
subsumption results in the side effect of type variables being unified by the
simplifier, we need to take care to clone the variables in the hole and relevant
constraints before checking whether an identifier fits into the hole, to avoid
affecting the hole and later checks. When outputting, we sort them by the
size of the types we'd need to apply to the type to make it fit. This is done in
order to display "more relevant" suggestions first.

When the flag `-frefinement-level-hole-fits=n` where `n > 0` is passed, we
also look for valid refinement hole fits, i.e. hole fits that are valid,
but adds more holes. Consider the following:

  f :: [Integer] -> Integer
  f = _

Here the valid hole fits suggested will be (with the
`-funclutter-valid-hole-fits` flag set):

  Valid hole fits include
    f :: [Integer] -> Integer
    head :: forall a. [a] -> a
    last :: forall a. [a] -> a
    maximum :: forall (t :: * -> *).
                Foldable t =>
                forall a. Ord a => t a -> a
    minimum :: forall (t :: * -> *).
                Foldable t =>
                forall a. Ord a => t a -> a
    product :: forall (t :: * -> *).
                Foldable t =>
                forall a. Num a => t a -> a
    sum :: forall (t :: * -> *).
            Foldable t =>
            forall a. Num a => t a -> a

When the `-frefinement-level-hole-fits=1` flag is given, we additionally
compute and report valid refinement hole fits:

  Valid refinement hole fits include

    foldl1 (_ :: Integer -> Integer -> Integer)
      with foldl1 @[] @Integer
      where foldl1 :: forall (t :: * -> *).
                      Foldable t =>
                      forall a. (a -> a -> a) -> t a -> a
    foldr1 (_ :: Integer -> Integer -> Integer)
      with foldr1 @[] @Integer
      where foldr1 :: forall (t :: * -> *).
                      Foldable t =>
                      forall a. (a -> a -> a) -> t a -> a
    const (_ :: Integer)
      with const @Integer @[Integer]
      where const :: forall a b. a -> b -> a
    ($) (_ :: [Integer] -> Integer)
      with ($) @'GHC.Types.LiftedRep @[Integer] @Integer
      where ($) :: forall a b. (a -> b) -> a -> b
    fail (_ :: String)
      with fail @((->) [Integer]) @Integer
      where fail :: forall (m :: * -> *).
                    Monad m =>
                    forall a. String -> m a
    return (_ :: Integer)
      with return @((->) [Integer]) @Integer
      where return :: forall (m :: * -> *). Monad m => forall a. a -> m a
    (Some refinement hole fits suppressed;
      use -fmax-refinement-hole-fits=N or -fno-max-refinement-hole-fits)

Which are hole fits with holes in them. This allows e.g. beginners to
discover the fold functions and similar.

We find these refinement suggestions by considering hole fits that don't
fit the type of the hole, but ones that would fit if given an additional
argument. We do this by creating a new type variable with `newOpenFlexiTyVarTy`
(e.g. `t_a1/m[tau:1]`), and then considering hole fits of the type
`t_a1/m[tau:1] -> v` where `v` is the type of the hole. Since the simplifier is
free to unify this new type variable with any type (and it is cloned before each
check to avoid side-effects), we can now discover any identifiers that would fit
if given another identifier of a suitable type. This is then generalized so that
we can consider any number of additional arguments by setting the
`-frefinement-level-hole-fits` flag to any number, and then considering
hole fits like e.g. `foldl _ _` with two additional arguments.


-}




data HoleFitDispConfig = HFDC { showWrap :: Bool
                              , showType :: Bool
                              , showProv :: Bool
                              , showMatches :: Bool }

debugHoleFitDispConfig :: HoleFitDispConfig
debugHoleFitDispConfig = HFDC True True False False


-- We read the various -no-show-*-of-hole-fits flags
-- and set the display config accordingly.
getHoleFitDispConfig :: TcM HoleFitDispConfig
getHoleFitDispConfig
  = do { sWrap <- goptM Opt_ShowTypeAppOfHoleFits
       ; sType <- goptM Opt_ShowTypeOfHoleFits
       ; sProv <- goptM Opt_ShowProvOfHoleFits
       ; sMatc <- goptM Opt_ShowMatchesOfHoleFits
       ; return HFDC{ showWrap = sWrap, showProv = sProv
                    , showType = sType, showMatches = sMatc } }

-- Which sorting algorithm to use
data SortingAlg = NoSorting      -- Do not sort the fits at all
                | BySize         -- Sort them by the size of the match
                | BySubsumption  -- Sort by full subsumption
                deriving (Eq, Ord)

getSortingAlg :: TcM SortingAlg
getSortingAlg =
    do { shouldSort <- goptM Opt_SortValidHoleFits
       ; subsumSort <- goptM Opt_SortBySubsumHoleFits
       ; sizeSort <- goptM Opt_SortBySizeHoleFits
       -- We default to sizeSort unless it has been explicitly turned off
       -- or subsumption sorting has been turned on.
       ; return $ if not shouldSort
                    then NoSorting
                    else if subsumSort
                         then BySubsumption
                         else if sizeSort
                              then BySize
                              else NoSorting }

-- HoleFit is the type we use for valid hole fits. It contains the
-- element that was checked, the Id of that element as found by `tcLookup`,
-- and the refinement level of the fit, which is the number of extra argument
-- holes that this fit uses (e.g. if hfRefLvl is 2, the fit is for `Id _ _`).
data HoleFit = HoleFit { hfElem :: Maybe GlobalRdrElt -- The element that was
                                                      -- if a global, nothing
                                                      -- if it is a local.
                       , hfId :: Id       -- The elements id in the TcM
                       , hfType :: TcType -- The type of the id, possibly zonked
                       , hfRefLvl :: Int  -- The number of holes in this fit
                       , hfWrap :: [TcType] -- The wrapper for the match
                       , hfMatches :: [TcType] } -- What the refinement
                                                 -- variables got matched with,
                                                 -- if anything

-- We define an Eq and Ord instance to be able to build a graph.
instance Eq HoleFit where
   (==) = (==) `on` hfId

-- We compare HoleFits by their gre_name instead of their Id, since we don't
-- want our tests to be affected by the non-determinism of `nonDetCmpVar`,
-- which is used to compare Ids. When comparing, we want HoleFits with a lower
-- refinement level to come first.
instance Ord HoleFit where
  compare a b = cmp a b
    where cmp  = if hfRefLvl a == hfRefLvl b
                 then compare `on` (idName . hfId)
                 else compare `on` hfRefLvl

instance Outputable HoleFit where
    ppr = pprHoleFit debugHoleFitDispConfig

instance (HasOccName a, HasOccName b) => HasOccName (Either a b) where
    occName = either occName occName

instance HasOccName GlobalRdrElt where
    occName = occName . gre_name

-- For pretty printing hole fits, we display the name and type of the fit,
-- with added '_' to represent any extra arguments in case of a non-zero
-- refinement level.
pprHoleFit :: HoleFitDispConfig -> HoleFit -> SDoc
pprHoleFit (HFDC sWrp sTy sProv sMs) hf = hang display 2 provenance
    where name = case hfElem hf of
                      Just gre -> gre_name gre
                      Nothing -> idName (hfId hf)
          ty = hfType hf
          matches =  hfMatches hf
          wrap = hfWrap hf
          tyApp = sep $ map ((text "@" <>) . pprParendType) wrap
          holeVs = sep $ map (parens . (text "_" <+> dcolon <+>) . ppr) matches
          holeDisp = if sMs then holeVs
                     else sep $ replicate (length matches) $ text "_"
          occDisp = pprPrefixOcc name
          tyDisp = ppWhen sTy $ dcolon <+> ppr ty
          has = not . null
          wrapDisp = ppWhen (sWrp && has wrap)
                      $ text "with" <+> occDisp <+> tyApp
          funcInfo = ppWhen (has matches) $
                       ppWhen sTy $ text "where" <+> occDisp <+> tyDisp
          subDisp = occDisp <+> if has matches then holeDisp else tyDisp
          display =  subDisp $$ nest 2 (wrapDisp $+$ funcInfo)
          provenance = ppWhen sProv $
            parens $
                case hfElem hf of
                    Just gre -> pprNameProvenance gre
                    Nothing -> text "bound at" <+> ppr (getSrcLoc name)

getLocalBindings :: TidyEnv -> Ct -> TcM [Id]
getLocalBindings tidy_orig ct
 = do { (env1, _) <- zonkTidyOrigin tidy_orig (ctLocOrigin loc)
      ; go env1 [] (removeBindingShadowing $ tcl_bndrs lcl_env) }
  where
    loc     = ctEvLoc (ctEvidence ct)
    lcl_env = ctLocEnv loc

    go :: TidyEnv -> [Id] -> [TcBinder] -> TcM [Id]
    go _ sofar [] = return (reverse sofar)
    go env sofar (tc_bndr : tc_bndrs) =
        case tc_bndr of
          TcIdBndr id _ -> keep_it id
          _ -> discard_it
     where
        discard_it = go env sofar tc_bndrs
        keep_it id = go env (id:sofar) tc_bndrs

-- See Note [Valid hole fits include ...]
findValidHoleFits :: TidyEnv        --The tidy_env for zonking
                           -> [Implication]  --Enclosing implications for givens
                           -> [Ct]           --Simple constraints for relevant
                                             --unsolved constraints
                           -> Ct             --The hole constraint
                           -> TcM (TidyEnv, SDoc)
findValidHoleFits tidy_env implics simples ct | isExprHoleCt ct =
  do { rdr_env <- getGlobalRdrEnv
     ; lclBinds <- getLocalBindings tidy_env ct
     ; maxVSubs <- maxValidHoleFits <$> getDynFlags
     ; hfdc <- getHoleFitDispConfig
     ; sortingAlg <- getSortingAlg
     ; refLevel <- refLevelHoleFits <$> getDynFlags
     ; traceTc "findingValidHoleFitsFor { " $ ppr ct
     ; traceTc "hole_lvl is:" $ ppr hole_lvl
     ; traceTc "implics are: " $ ppr implics
     ; traceTc "simples are: " $ ppr simples
     ; traceTc "locals are: " $ ppr lclBinds
     ; let to_check = map Left lclBinds ++ map Right (globalRdrEnvElts rdr_env)
     ; (searchDiscards, subs) <-
        findSubs sortingAlg maxVSubs to_check 0 (hole_ty, [])
     ; (tidy_env, tidy_subs) <- zonkSubs tidy_env subs
     ; (vDiscards, tidy_sorted_subs) <-
        sortFits sortingAlg maxVSubs searchDiscards tidy_subs
     ; let vMsg = ppUnless (null tidy_sorted_subs) $
                    hang (text "Valid hole fits include") 2 $
                      vcat (map (pprHoleFit hfdc) tidy_sorted_subs)
                        $$ ppWhen vDiscards subsDiscardMsg
     ; (tidy_env, refMsg) <- if refLevel >= Just 0 then
         do { maxRSubs <- maxRefHoleFits <$> getDynFlags
            -- We can use from just, since we know that Nothing >= _ is False.
            ; let refLvls = [1..(fromJust refLevel)]
            -- We make a new refinement type for each level of refinement, where
            -- the level of refinement indicates number of additional arguments
            -- to allow.
            ; ref_tys <- mapM (\l -> (,) l <$> mkRefTy l) refLvls
            ; traceTc "ref_tys are" $ ppr ref_tys
            ; refDs <- mapM
                         (uncurry $ findSubs sortingAlg maxRSubs to_check)
                         ref_tys
            ; (tidy_env, tidy_rsubs) <- zonkSubs tidy_env $ concatMap snd refDs
            ; (rDiscards, tidy_sorted_rsubs) <-
                sortFits sortingAlg maxRSubs (any fst refDs) tidy_rsubs
            ; return (tidy_env,
                ppUnless (null tidy_sorted_rsubs) $
                  hang (text "Valid refinement hole fits include") 2 $
                  vcat (map (pprHoleFit hfdc) tidy_sorted_rsubs)
                    $$ ppWhen rDiscards refSubsDiscardMsg) }
       else return (tidy_env, empty)
     ; traceTc "findingValidHoleFitsFor }" empty
     ; return (tidy_env, vMsg $$ refMsg) }
  where
    -- We extract the type, the tcLevel and the types free variables
    -- from from the constraint.
    hole_ty :: TcPredType
    hole_ty = ctPred ct
    hole_fvs = tyCoFVsOfType hole_ty
    hole_lvl = ctLocLevel $ ctEvLoc $ ctEvidence ct

    -- We make a refinement type by adding a new type variable in front
    -- of the type of t h hole, going from e.g. [Integer] -> Integer
    -- to t_a1/m[tau:1] -> [Integer] -> Integer. This allows the simplifier
    -- to unify the new type variable with any type, allowing us
    -- to suggest a "refinement hole fit", like `(foldl1 _)` instead
    -- of only concrete hole fits like `sum`.
    mkRefTy :: Int -> TcM (TcType, [TcType])
    mkRefTy refLvl = (\v -> (wrapHoleWithArgs v, v)) <$> newTyVarTys
      where newTyVarTys = replicateM refLvl $ mkTyVarTy . setLvl <$>
                            (newOpenTypeKind >>= newFlexiTyVar)
            setLvl = flip setMetaTyVarTcLevel hole_lvl
            wrapHoleWithArgs args = mkFunTys args hole_ty

    sortFits :: SortingAlg    -- How we should sort the hole fits
             -> Maybe Int     -- How many we should output, if limited.
             -> Bool          -- Whether there were any discards in the
                              -- initial search
             -> [HoleFit]     -- The subs to sort
             -> TcM (Bool, [HoleFit])
    -- If we don't want to sort, we just sort it
    -- such that local fits come before global fits, since local fits are
    -- probably more relevant to the user.
    sortFits NoSorting _ discards subs = return (discards, sortedFits)
        where (lclFits, gblFits) = partition isLocalHoleFit subs
              sortedFits = lclFits ++ gblFits
    sortFits BySize limit _ subs
        = possiblyDiscard limit <$>
            ((++) <$> sortBySize (sort lclFits)
                  <*> sortBySize (sort gblFits))
        where (lclFits, gblFits) = partition isLocalHoleFit subs
    -- We sort the fits first, to prevent the order of
    -- suggestions being effected when identifiers are moved
    -- around in modules. We use (<*>) to expose the
    -- parallelism, in case it becomes useful later.
    sortFits BySubsumption limit _ subs
        = possiblyDiscard limit <$>
            ((++) <$> sortByGraph (sort lclFits)
                  <*> sortByGraph (sort gblFits))
        where (lclFits, gblFits) = partition isLocalHoleFit subs

    findSubs :: SortingAlg         -- Whether we should sort the subs or not
             -> Maybe Int          -- How many we should output, if limited
             -> [Either Id GlobalRdrElt] -- The elements to check whether fit
             -> Int                -- The refinement level of the hole
             -> (TcType, [TcType]) -- The type to check for fits and refinement
                                   -- variables used to emulate additional holes
             -> TcM (Bool, [HoleFit]) -- We return whether or not we stopped due
                                      -- to running out of gas and the fits we
                                      -- found.
    -- We don't check if no output is desired.
    findSubs _ (Just 0) _ _ _ = return (False, [])
    findSubs sortAlg maxSubs to_check refLvl ht@(hole_ty, _) =
      do { traceTc "checkingFitsFor {" $ ppr hole_ty
         ; let limit = if sortAlg > NoSorting then Nothing else maxSubs
         ; (discards, subs) <- -- setTcLevel hole_lvl
             go limit ht refLvl to_check
         ; traceTc "}" empty
         ; return (discards, subs) }

    isLocalHoleFit :: HoleFit -> Bool
    isLocalHoleFit hf = case hfElem hf of
                          Just gre -> gre_lcl gre
                          Nothing -> True

    -- These are the constraints whose every free unification variable is
    -- mentioned in the type of the hole.
    
    --- SPJ: I have no idea what is happening here. Write a (separate) Note with an example 
    relevantCts :: [Ct]
    relevantCts = if isEmptyVarSet hole_fv then []
                  else filter isRelevant simples
      where hole_fv :: VarSet
            hole_fv = fvVarSet hole_fvs
            ctFreeVarSet :: Ct -> VarSet
            ctFreeVarSet = fvVarSet . tyCoFVsOfType . ctPred
            allFVMentioned :: Ct -> Bool
            allFVMentioned ct = ctFreeVarSet ct `subVarSet` hole_fv
            -- We filter out those constraints that have no variables (since
            -- they won't be solved by finding a type for the type variable
            -- representing the hole) and also other holes, since we're not
            -- trying to find hole fits for many holes at once.
            isRelevant ct = not (isEmptyVarSet (ctFreeVarSet ct))
                            && allFVMentioned ct
                            && not (isHoleCt ct)

    unfoldWrapper :: HsWrapper -> [Type]
    unfoldWrapper = reverse . unfWrp'
      where unfWrp' (WpTyApp ty) = [ty]
            unfWrp' (WpCompose w1 w2) = unfWrp' w1 ++ unfWrp' w2
            unfWrp' _ = []

    -- Takes a list of types and makes sure that the given action
    -- is run with the right TcLevel and restores any Flexi type
    -- variables after the action is run.
    withoutUnification :: [TcType] -> TcM a -> TcM a          
    withoutUnification tys action
      = do { flexis <- filterM isFlexiTyVar fuvs
           ; result <- setTcLevel deepestFreeTyVarLvl action
             -- Reset any mutated free variables
           ; mapM_  restore flexis 
           ; return result }
      where restore = flip writeTcRef Flexi . metaTyVarRef
            fuvs = fvVarList $ tyCoFVsOfTypes tys
            
            deepestFreeTyVarLvl = foldl' max topTcLevel $ map tcTyVarLevel fuvs
            

    -- We need to freshen the ev_binds of implications to make sure
    -- that we don't have side effects on them.
    freshenEvBinds :: Implication -> TcM Implication
    freshenEvBinds imp = do { nbinds <- newTcEvBinds
                            ; return imp {ic_binds = nbinds} }

    isFlexiTyVar :: TcTyVar -> TcM Bool
    isFlexiTyVar tv | isMetaTyVar tv = isFlexi <$> readMetaTyVar tv
    isFlexiTyVar _ = return False

    -- The real work happens here, where we invoke the type checker
    -- to check whether we the given type fits into the hole!
    -- To check: Clone all relevant cts and the hole
    -- then solve the subsumption check AND check that all other
    -- the other constraints were solved.
    fitsHole :: (TcType, [TcType]) -> Type -> TcM (Maybe ([TcType], [TcType]))
    fitsHole (h_ty, h_vars) ty =
      withoutUnification [h_ty, ty] $
      do { traceTc "checkingFitOf {" $ ppr ty
         ; fresh_implics <- mapM freshenEvBinds implics
         ; (absFits, wrp) <-
             tcCheckHoleFit (listToBag relevantCts) fresh_implics h_ty ty
         ; traceTc "Did it fit?" $ ppr absFits
         ; traceTc "wrap is: " $ ppr wrp
         ; traceTc "}" empty
         ; z_wrp_tys <- zonkTcTypes (unfoldWrapper wrp)
         -- We'd like to avoid refinement suggestions like `id _ _` or
         -- `head _ _`, and only suggest refinements where our all phantom
         -- variables got unified during the checking. This can be disabled
         -- with the `-fabstract-refinement-hole-fits` flag.
         ; if absFits then fmap ((, ) z_wrp_tys) <$>
           if null h_vars then return (Just []) else
            do { let fvsOfChecked = fvVarSet $ tyCoFVsOfTypes [h_ty, ty]
                     -- To be concrete matches, matches have to
                     -- be more than just an invented type variable.
                     notAbstract :: TcType -> Bool
                     notAbstract t = case getTyVar_maybe t of
                                       Just tv -> tv `elemVarSet` fvsOfChecked
                                       _ -> True
                     allConcrete = all notAbstract z_wrp_tys
                ; z_vars  <- zonkTcTypes h_vars
                ; let z_mtvs = mapMaybe tcGetTyVar_maybe z_vars
                ; allFilled <- not <$> anyM isFlexiTyVar z_mtvs
                ; allowAbstract <- goptM Opt_AbstractRefHoleFits
                ; if allowAbstract || (allFilled && allConcrete )
                  then return $ Just z_vars
                  else return Nothing }
            else return Nothing }

    -- We zonk the hole fits so that the output aligns with the rest
    -- of the typed hole error message output.
    zonkSubs :: TidyEnv -> [HoleFit] -> TcM (TidyEnv, [HoleFit])
    zonkSubs = zonkSubs' []
      where zonkSubs' zs env [] = return (env, reverse zs)
            zonkSubs' zs env (hf:hfs) = do { (env', z) <- zonkSub env hf
                                           ; zonkSubs' (z:zs) env' hfs }
            zonkSub env hf@HoleFit{hfType = ty, hfMatches = m, hfWrap = wrp}
              = do { (env, ty') <- zonkTidyTcType env ty
                   ; (env, m') <- zonkTidyTcTypes env m
                   ; (env, wrp') <- zonkTidyTcTypes env wrp
                   ; let zFit = hf {hfType = ty', hfMatches = m', hfWrap = wrp' }
                   ; return (env, zFit ) }

    -- Based on the flags, we might possibly discard some or all the
    -- fits we've found.
    possiblyDiscard :: Maybe Int -> [HoleFit] -> (Bool, [HoleFit])
    possiblyDiscard (Just max) fits = (fits `lengthExceeds` max, take max fits)
    possiblyDiscard Nothing fits = (False, fits)


    -- Sort by size uses as a measure for relevance the sizes of the
    -- different types needed to instantiate the fit to the type of the hole.
    -- This is much quicker than sorting by subsumption, and gives reasonable
    -- results in most cases.
    sortBySize :: [HoleFit] -> TcM [HoleFit]
    sortBySize = return . sortOn sizeOfFit
      where sizeOfFit :: HoleFit -> TypeSize
            sizeOfFit = sizeTypes . nubBy tcEqType .  hfWrap

    -- Based on a suggestion by phadej on #ghc, we can sort the found fits
    -- by constructing a subsumption graph, and then do a topological sort of
    -- the graph. This makes the most specific types appear first, which are
    -- probably those most relevant. This takes a lot of work (but results in
    -- much more useful output), and can be disabled by
    -- '-fno-sort-valid-hole-fits'.
    sortByGraph :: [HoleFit] -> TcM [HoleFit]
    sortByGraph fits = go [] fits
      where tcSubsumesWCloning :: TcType -> TcType -> TcM Bool
            tcSubsumesWCloning ht ty =
              withoutUnification [ht, ty] $ do { z_ht <- zonkTcType ht
                                               ; z_ty <- zonkTcType ty
                                               ; tcSubsumes z_ht z_ty }
            go :: [(HoleFit, [HoleFit])] -> [HoleFit] -> TcM [HoleFit]
            go sofar [] = do { traceTc "subsumptionGraph was" $ ppr sofar
                             ; return $ uncurry (++)
                                         $ partition isLocalHoleFit topSorted }
              where toV (hf, adjs) = (hf, hfId hf, map hfId adjs)
                    (graph, fromV, _) = graphFromEdges $ map toV sofar
                    topSorted = map ((\(h,_,_) -> h) . fromV) $ topSort graph
            go sofar (hf:hfs) =
              do { adjs <-
                     filterM (tcSubsumesWCloning (hfType hf) . hfType) fits
                 ; go ((hf, adjs):sofar) hfs }

    -- Kickoff the checking of the elements.
    go :: Maybe Int -> (TcType, [TcType]) -> Int
        -> [Either Id GlobalRdrElt] -> TcM (Bool, [HoleFit])
    go limit ty rlvl = go_ [] emptyVarSet limit ty rlvl . removeBindingShadowing

    -- We iterate over the elements, checking each one in turn for whether it
    -- fits, and adding it to the results if it does.
    go_ :: [HoleFit]          -- What we've found so far.
        -> VarSet             -- Ids we've already checked
        -> Maybe Int          -- How many we're allowed to find, if limited
        -> (TcType, [TcType]) -- The type to check, and refinement variables.
        -> Int                -- The refinement level of the hole we're checking
        -> [Either Id GlobalRdrElt]     -- The elements we've yet to check.
        -> TcM (Bool, [HoleFit])
    go_ subs _ _ _ _ [] = return (False, reverse subs)
    go_ subs _ (Just 0) _ _ _ = return (True, reverse subs)
    go_ subs seen maxleft ty rlvl (el:elts) =
      do { traceTc "lookingUp" $ ppr el
         ; maybeThing <- lookup el
         ; case maybeThing of
             Just id | not_trivial id ->
                       do { fits <- fitsHole ty (idType id)
                          ; case fits of
                              Just (wrp, matches) -> keep_it id wrp matches
                              _ -> discard_it }
             _ -> discard_it }
      where discard_it = go_ subs seen maxleft ty rlvl elts
            keep_it id wrp ms = go_ (fit:subs) (extendVarSet seen id)
                              ((\n -> n - 1) <$> maxleft) ty rlvl elts
              where fit = HoleFit { hfElem = mbel , hfId = id
                                  , hfType = idType id , hfRefLvl = rlvl
                                  , hfWrap = wrp , hfMatches = ms }
                    mbel = either (const Nothing) Just el
            -- We want to filter out undefined.
            not_trivial id = nameModule_maybe (idName id) /= Just gHC_ERR
            lookup :: Either Id GlobalRdrElt -> TcM (Maybe Id)
            lookup (Left id) = return $ Just id
            lookup (Right el) =
              do { thing <- tcLookup (gre_name el)
                 ; case thing of
                     ATcId {tct_id = id} -> return $ Just id
                     AGlobal (AnId id)   -> return $ Just id
                     AGlobal (AConLike (RealDataCon con))  ->
                       return $ Just (dataConWrapId con)
                     _ -> return Nothing }


-- We don't (as of yet) handle holes in types, only in expressions.
findValidHoleFits env _ _ _ = return (env, empty)

subsDiscardMsg :: SDoc
subsDiscardMsg =
    text "(Some hole fits suppressed;" <+>
    text "use -fmax-valid-hole-fits=N" <+>
    text "or -fno-max-valid-hole-fits)"

refSubsDiscardMsg :: SDoc
refSubsDiscardMsg =
    text "(Some refinement hole fits suppressed;" <+>
    text "use -fmax-refinement-hole-fits=N" <+>
    text "or -fno-max-refinement-hole-fits)"


