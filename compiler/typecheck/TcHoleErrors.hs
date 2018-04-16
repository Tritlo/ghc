{-# OPTIONS_GHC -fno-warn-orphans #-} -- We don't want to spread the HasOccName
                                      -- instance for Either
module TcHoleErrors ( findValidHoleSubstitutions ) where

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
import TcSMonad ( getTcEvBindsVar, runTcS )


import PrelNames ( gHC_ERR )
import Id
import Var
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
import Data.List        ( partition, sort, sortOn, nubBy )
import Data.Graph       ( graphFromEdges, topSort )
import Data.Function    ( on )

-- SPJ
-- This is a super-important Note. Can you put it at the top of this module?
-- And review it carefully to make sure it really describes all the moving parts. Including the business about building an implication constraint, with an example or two to support it.

{-
Note [Valid substitutions include ...]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
`validSubstitutions` returns the "Valid substitutions include ..." message.
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
    Valid substitutions include
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

Valid substitutions are found by checking top level identifiers in scope for
whether their type is subsumed by the type of the hole. Additionally, as
highlighted by Trac #14273, we also need to check whether all relevant
constraints are solved by choosing an identifier of that type as well. This is
to make sure we don't suggest a substitution which does not fulfill the
constraints imposed on the hole (even though it has a type that would otherwise
fit the hole). The relevant constraints are those whose free unification
variables are all mentioned by the type of the hole. Since checking for
subsumption results in the side effect of type variables being unified by the
simplifier, we need to take care to clone the variables in the hole and relevant
constraints before checking whether an identifier fits into the hole, to avoid
affecting the hole and later checks. When outputting, we sort them by the
size of the types we'd need to apply to the type to make it fit. This is done in
order to display "more relevant" suggestions first.

When the flag `-frefinement-level-substitutions=n` where `n > 0` is passed, we
also look for valid refinement substitutions, i.e. substitutions that are valid,
but adds more holes. Consider the following:

  f :: [Integer] -> Integer
  f = _

Here the valid substitutions suggested will be (with the
`-funclutter-valid-substitutions` flag set):

  Valid substitutions include

  Valid substitutions include
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

When the `-frefinement-level-substitutions=1` flag is given, we additionally
compute and report valid refinement substitutions:

  Valid refinement substitutions include

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
    (Some refinement substitutions suppressed;
      use -fmax-refinement-substitutions=N or -fno-max-refinement-substitutions)

Which are substitutions with holes in them. This allows e.g. beginners to
discover the fold functions and similar.

We find these refinement suggestions by considering substitutions that don't
fit the type of the hole, but ones that would fit if given an additional
argument. We do this by creating a new type variable with `newOpenFlexiTyVarTy`
(e.g. `t_a1/m[tau:1]`), and then considering substitutions of the type
`t_a1/m[tau:1] -> v` where `v` is the type of the hole. Since the simplifier is
free to unify this new type variable with any type (and it is cloned before each
check to avoid side-effects), we can now discover any identifiers that would fit
if given another identifier of a suitable type. This is then generalized so that
we can consider any number of additional arguments by setting the
`-frefinement-level-substitutions` flag to any number, and then considering
substitutions like e.g. `foldl _ _` with two additional arguments.


-}




data HoleFitDispConfig = HFDC { showWrap :: Bool
                              , showType :: Bool
                              , showProv :: Bool
                              , showMatches :: Bool }

debugHoleFitDispConfig :: HoleFitDispConfig
debugHoleFitDispConfig = HFDC True True False False


-- We read the various -no-show-*-of-substitutions flags
-- and set the display config accordingly.
getHoleFitDispConfig :: TcM HoleFitDispConfig
getHoleFitDispConfig
  = do { sWrap <- goptM Opt_ShowTypeAppOfSubstitutions
       ; sType <- goptM Opt_ShowTypeOfSubstitutions
       ; sProv <- goptM Opt_ShowProvOfSubstitutions
       ; sMatc <- goptM Opt_ShowMatchesOfSubstitutions
       ; return HFDC{ showWrap = sWrap, showProv = sProv
                    , showType = sType, showMatches = sMatc } }

-- Which sorting algorithm to use
data SortingAlg = NoSorting      -- Do not sort the fits at all
                | BySize         -- Sort them by the size of the match
                | BySubsumption  -- Sort by full subsumption
                deriving (Eq, Ord)

getSortingAlg :: TcM SortingAlg
getSortingAlg =
    do { shouldSort <- goptM Opt_SortValidSubstitutions
       ; subsumSort <- goptM Opt_SortBySubsumSubstitutions
       ; sizeSort <- goptM Opt_SortBySizeSubstitutions
       -- We default to sizeSort unless it has been explicitly turned off
       -- or subsumption sorting has been turned on.
       ; return $ if not shouldSort
                    then NoSorting
                    else if subsumSort
                         then BySubsumption
                         else if sizeSort
                              then BySize
                              else NoSorting }

-- HoleFit is the type we use for a fit in valid substitutions. It contains the
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

setTcTyVarLevel :: TcTyVar -> TcLevel -> TcTyVar
setTcTyVarLevel tv nlvl =
  case tcTyVarDetails tv of
    MetaTv {} -> setMetaTyVarTcLevel tv nlvl
    SkolemTv _ b -> setTcTyVarDetails tv (SkolemTv nlvl b)
    RuntimeUnk -> tv

-- See Note [Valid substitutions include ...]
findValidHoleSubstitutions :: TidyEnv        --The tidy_env for zonking
                           -> [Implication]  --Enclosing implications for givens
                           -> [Ct]           --Simple constraints for relevant
                                             --unsolved constraints
                           -> Ct             --The hole constraint
                           -> TcM (TidyEnv, SDoc)
findValidHoleSubstitutions tidy_env implics simples ct | isExprHoleCt ct =
  do { rdr_env <- getGlobalRdrEnv
     ; lclBinds <- getLocalBindings tidy_env ct
     ; maxVSubs <- maxValidSubstitutions <$> getDynFlags
     ; hfdc <- getHoleFitDispConfig
     ; sortingAlg <- getSortingAlg
     ; refLevel <- refLevelSubstitutions <$> getDynFlags
     ; traceTc "findingValidSubstitutionsFor { " $ ppr ct
     ; traceTc "hole_lvl is:" $ ppr hole_lvl
     ; traceTc "implics are: " $ ppr implics
     ; traceTc "simples are: " $ ppr simples
     ; traceTc "locals are: " $ ppr lclBinds
     ; let to_check = map Left lclBinds ++ map Right (globalRdrEnvElts rdr_env)
     ; (searchDiscards, subs) <-
        findSubs sortingAlg maxVSubs to_check 0 (hole_ty, [])
     ; (tidy_env, tidy_subs) <- zonkSubs tidy_env subs
     ; (vDiscards, tidy_sorted_subs) <-
        sortSubs sortingAlg maxVSubs searchDiscards tidy_subs
     ; let vMsg = ppUnless (null tidy_sorted_subs) $
                    hang (text "Valid substitutions include") 2 $
                      vcat (map (pprHoleFit hfdc) tidy_sorted_subs)
                        $$ ppWhen vDiscards subsDiscardMsg
     ; (tidy_env, refMsg) <- if refLevel >= Just 0 then
         do { maxRSubs <- maxRefSubstitutions <$> getDynFlags
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
                sortSubs sortingAlg maxRSubs (any fst refDs) tidy_rsubs
            ; return (tidy_env,
                ppUnless (null tidy_sorted_rsubs) $
                  hang (text "Valid refinement substitutions include") 2 $
                  vcat (map (pprHoleFit hfdc) tidy_sorted_rsubs)
                    $$ ppWhen rDiscards refSubsDiscardMsg) }
       else return (tidy_env, empty)
     ; traceTc "findingValidSubstitutionsFor }" empty
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
    -- to suggest a "refinement substitution", like `(foldl1 _)` instead
    -- of only concrete substitutions like `sum`.
    mkRefTy :: Int -> TcM (TcType, [TcType])
    mkRefTy refLvl = (\v -> (wrapHoleWithArgs v, v)) <$> newTyVarTys
     where newTyVarTys
             =
             replicateM refLvl $ mkTyVarTy . setLvl <$>
                (newOpenTypeKind >>= newFlexiTyVar)
           setLvl = flip setTcTyVarLevel hole_lvl
           wrapHoleWithArgs args = mkFunTys args hole_ty


    sortSubs :: SortingAlg    -- How we should sort the substitutions
             -> Maybe Int     -- How many we should output, if limited.
             -> Bool          -- Whether there were any discards in the
                              -- initial search
             -> [HoleFit]     -- The subs to sort
             -> TcM (Bool, [HoleFit])
    -- If we don't want to sort, we just sort it
    -- such that local fits come before global fits, since local fits are
    -- probably more relevant to the user.
    sortSubs NoSorting _ discards subs = return (discards, sortedFits)
        where (lclFits, gblFits) = partition isLocalHoleFit subs
              sortedFits = lclFits ++ gblFits
    sortSubs BySize limit _ subs
        = possiblyDiscard limit <$>
            ((++) <$> sortBySize (sort lclFits)
                  <*> sortBySize (sort gblFits))
        where (lclFits, gblFits) = partition isLocalHoleFit subs
    -- We sort the fits first, to prevent the order of
    -- suggestions being effected when identifiers are moved
    -- around in modules. We use (<*>) to expose the
    -- parallelism, in case it becomes useful later.
    sortSubs BySubsumption limit _ subs
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
      do { traceTc "checkingSubstitutionsFor {" $ ppr hole_ty
         ; let limit = if sortAlg > NoSorting then Nothing else maxSubs
         ; (discards, subs) <- setTcLevel hole_lvl $
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
            -- trying to find substitutions for many holes at once.
            isRelevant ct = not (isEmptyVarSet (ctFreeVarSet ct))
                            && allFVMentioned ct
                            && not (isHoleCt ct)


    -- This creates a substitution with new fresh type variables for all the
    -- free variables mentioned in the type of hole and in the relevant
    -- constraints. Note that since we only pick constraints such that all their
    -- free variables are mentioned by the hole, the free variables of the hole
    -- are all the free variables of the constraints as well.

    -- SPJ: Why do we need this substitution? Explain in a Note with an example. arc lint
    -- Why return TWO substitutions?
    getHoleCloningSubst :: [TcType] -> TcM (TCvSubst, TCvSubst)
    getHoleCloningSubst tys
      = do { cVars <- getClonedVars
           ; let sub = mkSub cVars
                 invSub = mkSub $ map flipPair cVars
           ; return (sub, invSub) }
      where cloneFV :: TcTyVar -> TcM (TcTyVar, TcTyVar)
            -- The subsumption check pushes the level, so as to be sure that
            -- its invocation of the solver doesn't unify type variables
            -- floating about that are unrelated to the subsumption check.
            -- However, these -- cloned variables in the hole type *should* be
            -- unified, so we make sure to bump the level before creating them.
            cloneFV fv = (,) fv . setLvl <$> cloneMetaTyVar fv
              where setLvl tv = setTcTyVarLevel tv hole_lvl
            -- We only need to clone meta type variables
            -- since we don't have any side effects on the others.
            getClonedVars :: TcM [(TyVar, TyVar)]
            getClonedVars = mapM cloneFV $
                              filter isMetaTyVar $
                                fvVarList $ tyCoFVsOfTypes tys
            flipPair (a,b) = (b,a)
            mkSub = mkTvSubstPrs . map (fmap mkTyVarTy)

    -- To pass along the givens in a way that works with local bindings,
    -- we have to clone the implications, and then nest our solve withing
    -- these implications.
    cloneImplic :: TCvSubst -> Implication -> TcM Implication
    cloneImplic subst Implic { ic_skols = tvs
                             , ic_given = given
                             , ic_wanted = wanted
                             , ic_tclvl = tlvl
                             , ic_info = info
                             , ic_env = env }
      = do { (nbinds, _) <- runTcS getTcEvBindsVar
           ; cWc <- substWC subst wanted
           ; return $ newImplication { ic_skols = tvs
                                     , ic_tclvl = tlvl
                                     , ic_given = map (substEvVar subst) given
                                     , ic_wanted = cWc
                                     , ic_info = substSkolemInfo subst info
                                     , ic_env = env
                                     , ic_binds = nbinds } }
        where -- Taken from Inst.hs in 7.6.3
              substSkolemInfo :: TCvSubst -> SkolemInfo -> SkolemInfo
              substSkolemInfo subst (SigSkol cx ty nm)
                = SigSkol cx (substTyAddInScope subst ty) nm
              substSkolemInfo subst (InferSkol ids)
                = InferSkol (mapSnd (substTyAddInScope subst) ids)
              substSkolemInfo _     info            = info

              substWC subst (WC simp impl) =
                   WC (mapBag (substCt subst) simp) <$>
                   mapBagM (cloneImplic subst) impl


              substEvVar sub var = setVarType var
                (substTyAddInScope sub $ varType var)


    -- This applies the given substitution to the given constraint.
    substCt :: TCvSubst -> Ct -> Ct
    substCt sub ct = ct {cc_ev = ev {ctev_pred = subbedPredType} }
      where subbedPredType = substTyAddInScope sub $ ctPred ct
            ev = ctEvidence ct

    unfoldWrapper :: HsWrapper -> [Type]
    unfoldWrapper = reverse . unfWrp'
      where unfWrp' (WpTyApp ty) = [ty]
            unfWrp' (WpCompose w1 w2) = unfWrp' w1 ++ unfWrp' w2
            unfWrp' _ = []

    -- To prevent the side-effective unification of type variables
    -- while checking whether a 
    withoutUnification :: [TcType] -> TcM a -> TcM a          
    withoutUnification tys action
      = do { result <- action
             -- Reset any mutated free variables
           ; mapM_  restore fuvs
           ; return result }
      where restore = flip writeTcRef Flexi . metaTyVarRef
            fuvs = fvVarList $ tyCoFVsOfTypes tys
                          
    -- The real work happens here, where we invoke the type checker
    -- to check whether we the given type fits into the hole!
    -- To check: Clone all relevant cts and the hole
    -- then solve the subsumption check AND check that all other
    -- the other constraints were solved.
    fitsHole :: (TcType, [TcType]) -> Type -> TcM (Maybe ([TcType], [TcType]))
    fitsHole (h_ty,h_vars) ty =
      withoutUnification [h_ty, ty] $
      do { traceTc "checkingFitOf {" $ ppr ty
         ; traceTc "tys before are: " $ ppr (h_ty, ty)
         ; traceTc "cvars are: " $ ppr h_vars
         ; traceTc "holeLvl" $ ppr hole_lvl
         -- We zonk in case the types refer to a filled type variable
         ; z_ty <- zonkTcType ty
         ; z_h_ty <- zonkTcType h_ty
         -- We need to clone the type variables to avoid side effects
         -- On the type variables in the hole during simplification
         ; (cloneSub, invSub) <- getHoleCloningSubst [z_h_ty, z_ty]
         ; z_cts <- mapM zonkCt relevantCts
         ; let cHoleTy = substTyAddInScope cloneSub z_h_ty
               cCts = map (substCt cloneSub) z_cts
               cVars = map (substTyAddInScope cloneSub) h_vars
               cTy = substTyAddInScope cloneSub z_ty
         ; cImp <- mapM (cloneImplic cloneSub) implics
         ; traceTc "sub is:" $ ppr cloneSub
         ; (absFits, wrp) <- tcCheckHoleFit (listToBag cCts) cImp cHoleTy cTy
         ; traceTc "Did it fit?" $ ppr absFits
         ; traceTc "tys after are:" $ ppr (cHoleTy, cTy)
         ; traceTc "wrap is: " $ ppr wrp
         ; traceTc "}" empty
        -- We apply the inverse substitution to match the cloned variables back
        -- to the originals

         ; zonkedWrpTys <- zonkTcTypes (unfoldWrapper wrp)
         ; let invSubbedWrp = map (substTyAddInScope invSub) zonkedWrpTys
         -- We'd like to avoid refinement suggestions like `id _ _` or
         -- `head _ _`, and only suggest refinements where our all phantom
         -- variables got unified during the checking. This can be disabled
         -- with the `-fabstract-refinement-substitutions` flag.
         ; if absFits then
           if null cVars then return (Just (invSubbedWrp, [])) else
            do { let mtvs :: [TyVar]
                     mtvs = mapMaybe tcGetTyVar_maybe cVars
                     getMTy :: MetaDetails -> Maybe TcType
                     getMTy Flexi = Nothing
                     getMTy (Indirect t) = Just t

                     fvsOfChecked = fvVarSet $ tyCoFVsOfType cHoleTy
                     -- To be concrete matches, matches have to
                     -- be more than just an invented type variable.
                     notAbstract :: TcType -> Bool
                     notAbstract t = case getTyVar_maybe t of
                                       Just tv -> tv `elemVarSet` fvsOfChecked
                                       _ -> True
                ; matches <- mapM (fmap getMTy . readMetaTyVar) mtvs
                ; allowAbstract <- goptM Opt_AbstractRefSubstitutions
                ; zonkedMatches <- zonkTcTypes $ catMaybes matches
                ; let allFilled = all isJust matches
                      allConcrete = all notAbstract zonkedWrpTys
                      invSubbedMs = map (substTyAddInScope invSub) zonkedMatches
                ; return $ if allowAbstract || (allFilled && allConcrete )
                           then Just (invSubbedWrp, invSubbedMs)
                           else Nothing }
            else return Nothing }

    -- We zonk the substitutions so that the output aligns with the rest
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
    -- '-fno-sort-valid-substitutions'.
    sortByGraph :: [HoleFit] -> TcM [HoleFit]
    sortByGraph fits = go [] fits
      where tcSubsumesWCloning :: TcType -> TcType -> TcM Bool
            tcSubsumesWCloning ht ty =
              do { z_ht <- zonkTcType ht
                 ; z_ty <- zonkTcType ty
                 ; (cloneSub, _) <- getHoleCloningSubst [z_ht, z_ty]
                 ; let cht = substTyAddInScope cloneSub z_ht
                       cty = substTyAddInScope cloneSub z_ty
                 ; setTcLevel hole_lvl $ tcSubsumes cht cty }
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
findValidHoleSubstitutions env _ _ _ = return (env, empty)

subsDiscardMsg :: SDoc
subsDiscardMsg =
    text "(Some substitutions suppressed;" <+>
    text "use -fmax-valid-substitutions=N" <+>
    text "or -fno-max-valid-substitutions)"

refSubsDiscardMsg :: SDoc
refSubsDiscardMsg =
    text "(Some refinement substitutions suppressed;" <+>
    text "use -fmax-refinement-substitutions=N" <+>
    text "or -fno-max-refinement-substitutions)"


