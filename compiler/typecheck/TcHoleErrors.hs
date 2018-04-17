{-# OPTIONS_GHC -fno-warn-orphans #-} -- We don't want to spread the HasOccName
                                      -- instance for Either
module TcHoleErrors ( findValidHoleFits ) where

import GhcPrelude

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
import ConLike          ( ConLike(..) )
import Util
import TcEnv (tcLookup)
import Outputable
import DynFlags
import Maybes
import FV ( fvVarList, fvVarSet, unionFV, mkFVs, FV )

import Control.Arrow ( (&&&) )

import Control.Monad    ( filterM, replicateM )
import Data.List        ( partition, sort, sortOn, nubBy, foldl' )
import Data.Graph       ( graphFromEdges, topSort )
import Data.Function    ( on )


import TcSimplify    ( simpl_top, runTcSDeriveds, isSolvedWC )
import TcUnify       ( tcSubType_NC )

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

Valid hole fits are found by checking top level identifiers and local bindings
in scope for whether their type is subsumed by the type of the hole.
Additionally, we also need to check whether all relevant constraints are solved
by choosing an identifier of that type as well, see Note [Relevant Constraints]

Since checking for subsumption results in the side-effect of type variables
being unified by the simplifier, we need to take care to restore them after
to being flexible type variables after we've checked for subsumption.
This is to avoid affecting the hole and later checks by prematurely having
unified one of the free unification variables.

For the simplifier to be able to use any givens present in the enclosing
implications to solve relevant constraints, we nest the wanted subsumption
constraints and relevant constraints within the enclosing implications. However
to avoid side-effects on those implications, we must freshen their EvBindsVar by
creating a new EvBindsVar which is then discarded after the check.


When outputting, we sort the hole fits by the size of the types we'd need to
apply by type application to the type of the fit to to make it fit. This is done
in order to display "more relevant" suggestions first. Another option is to
sort by building a subsumption graph of fits, i.e. a graph of which fits subsume
what other fits, and then outputting those fits which are subsumed by other fits
first. This results in the most specific fits, the ones "closest" to the type
of the hole to bee displayed first.

To help users understand how the suggested fit works, we also display the values
that the quantified type variables would take if that fit is used, like
`mempty @([Char] -> [String])` and `pure @[] @String` in the example above.
If -XTypeApplications is enabled, this can even be copied verbatim as a
replacement for the hole.


Note [Valid refinement hole fits include ...]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
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
discover the fold functions and similar, but also allows for advanced users
to figure out the valid functions in the Free monad, e.g.

  instance Functor f => Monad (Free f) where
      Pure a >>= f = f a
      Free f >>= g = Free (fmap _a f)

Will output (with -frefinment-level-hole-fits=1):
    Found hole: _a :: Free f a -> Free f b
          Where: ‘a’, ‘b’ are rigid type variables bound by
                  the type signature for:
                    (>>=) :: forall a b. Free f a -> (a -> Free f b) -> Free f b
                  at fms.hs:25:12-14
                ‘f’ is a rigid type variable bound by
    ...
    Relevant bindings include
      g :: a -> Free f b (bound at fms.hs:27:16)
      f :: f (Free f a) (bound at fms.hs:27:10)
      (>>=) :: Free f a -> (a -> Free f b) -> Free f b
        (bound at fms.hs:25:12)
    ...
    Valid refinement hole fits include
      ...
      (=<<) (_ :: a -> Free f b)
        with (=<<) @(Free f) @a @b
        where (=<<) :: forall (m :: * -> *) a b.
                      Monad m =>
                      (a -> m b) -> m a -> m b
        (imported from ‘Prelude’ at fms.hs:5:18-22
        (and originally defined in ‘GHC.Base’))
      ...

Where `(=<<) _` is precisely the function we want (we ultimately want `>>= g`).

We find these refinement suggestions by considering hole fits that don't
fit the type of the hole, but ones that would fit if given an additional
argument. We do this by creating a new type variable with `newOpenFlexiTyVar`
(e.g. `t_a1/m[tau:1]`), and then considering hole fits of the type
`t_a1/m[tau:1] -> v` where `v` is the type of the hole.

Since the simplifier is free to unify this new type variable with any type, we
can discover any identifiers that would fit if given another identifier of a
suitable type. This is then generalized so that we can consider any number of
additional arguments by setting the `-frefinement-level-hole-fits` flag to any
number, and then considering hole fits like e.g. `foldl _ _` with two additional
arguments.

To make sure that the refinement hole fits are useful, we check that the types
of the additional holes have a concrete value and not just an invented type
variable. This eliminates suggestions such as `head (_ :: [t0 -> a]) (_ :: t0)`,
and limits the number of less than useful refinement hole fits.

Additionally, to further aid the user in their implementation, we show the
types of the holes the binding would have to be applied to in order to work.
In the free monad example above, this is demonstrated with
`(=<<) (_ :: a -> Free f b)`, which tells the user that the `(=<<)` needs to
be applied to an expression of type `a -> Free f b` in order to match.
If -XScopedTypeVariables is enabled, this hole fit can even be copied verbatim.


Note [Relevant Constraints]
~~~~~~~~~~~~~~~~~~~

As highlighted by Trac #14273, we need to check any relevant constraints as well
as checking for subsumption. Relevant constraints are the simple constraints
whose free unification variables are mentioned in the type of the hole. These
are then the constraints for which any type that subsumes the type of the hole
has to fulfill in order to be a valid hole fit. We only check relevant
constraints so that e.g. when there are multiple holes, we can still find fits
for each of those holes. This is to make sure we don't suggest a hole fit which
does not fulfill the constraints imposed on the hole (even though it has a type
that would otherwise fit the hole).

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
                           -> [Ct] -- The  unsolved simple constraints in the
                                   -- implication for the hole.
                           -> Ct   -- The hole constraint itself
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
     ; let (lcl, gbl) = partition gre_lcl (globalRdrEnvElts rdr_env)
           -- We remove binding shadowings here, but only for the local level.
           -- this is so we e.g. suggest the global fmap from the Functor class
           -- even though there is a local definition as well, such as in the
           -- Free monad example.
           locals = map Left lclBinds ++ map Right lcl
           globals = map Right gbl
           to_check = removeBindingShadowing locals ++ globals
     ; (searchDiscards, subs) <-
        findSubs sortingAlg maxVSubs to_check (hole_ty, [])
     ; (tidy_env, tidy_subs) <- zonkSubs tidy_env subs
     ; (vDiscards, tidy_sorted_subs) <-
        sortFits sortingAlg maxVSubs searchDiscards tidy_subs
     ; let vMsg = ppUnless (null tidy_sorted_subs) $
                    hang (text "Valid hole fits include") 2 $
                      vcat (map (pprHoleFit hfdc) tidy_sorted_subs)
                        $$ ppWhen vDiscards subsDiscardMsg
     -- Refinement hole fits. See Note [Valid refinement hole fits include ...]
     ; (tidy_env, refMsg) <- if refLevel >= Just 0 then
         do { maxRSubs <- maxRefHoleFits <$> getDynFlags
            -- We can use from just, since we know that Nothing >= _ is False.
            ; let refLvls = [1..(fromJust refLevel)]
            -- We make a new refinement type for each level of refinement, where
            -- the level of refinement indicates number of additional arguments
            -- to allow.
            ; ref_tys <- mapM mkRefTy refLvls
            ; traceTc "ref_tys are" $ ppr ref_tys
            ; refDs <- mapM (findSubs sortingAlg maxRSubs to_check) ref_tys
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
    mkRefTy :: Int -> TcM (TcType, [TcTyVar])
    mkRefTy refLvl = (wrapWithVars &&& id) <$> newTyVars
      where newTyVars = replicateM refLvl $ setLvl <$>
                            (newOpenTypeKind >>= newFlexiTyVar)
            setLvl = flip setMetaTyVarTcLevel hole_lvl
            wrapWithVars vars = mkFunTys (map mkTyVarTy vars) hole_ty

    sortFits :: SortingAlg    -- How we should sort the hole fits
             -> Maybe Int     -- How many we should output, if limited.
             -> Bool          -- Whether there were any discards in the
                              -- initial search
             -> [HoleFit]     -- The subs to sort
             -> TcM (Bool, [HoleFit])

    sortFits NoSorting _ discards subs = return (discards, subs)
    sortFits BySize limit _ subs
        = possiblyDiscard limit <$>
            ((++) <$> sortBySize (sort lclFits)
                  <*> sortBySize (sort gblFits))
        where (lclFits, gblFits) = span isLocalHoleFit subs

    -- To sort by subsumption, we invoke the sortByGraph function, which
    -- builds the subsumption graph for the fits and then sorts them using a
    -- graph sort.  Since we want locals to come first anyway, we can sort
    -- them separately. The substitutions are already checked in local then
    -- global order, so we can get away with using span here.
    -- We use (<*>) to expose the parallelism, in case it becomes useful later.
    sortFits BySubsumption limit _ subs
        = possiblyDiscard limit <$>
            ((++) <$> sortByGraph (sort lclFits)
                  <*> sortByGraph (sort gblFits))
        where (lclFits, gblFits) = span isLocalHoleFit subs

    findSubs :: SortingAlg         -- Whether we should sort the subs or not
             -> Maybe Int          -- How many we should output, if limited
             -> [Either Id GlobalRdrElt] -- The elements to check whether fit
             -> (TcType, [TcTyVar]) -- The type to check for fits and refinement
                                    -- variables for emulating additional holes
             -> TcM (Bool, [HoleFit]) -- We return whether or not we stopped due
                                      -- to running out of gas and the fits we
                                      -- found.
    -- We don't check if no output is desired.
    findSubs _ (Just 0) _ _ = return (False, [])
    findSubs sortAlg maxSubs to_check ht@(hole_ty, _) =
      do { traceTc "checkingFitsFor {" $ ppr hole_ty
         -- If we're not going to sort anyway, we can stop going after
         -- having found `maxSubs` hole fits.
         ; let limit = if sortAlg > NoSorting then Nothing else maxSubs
         ; (discards, subs) <- go limit ht to_check
         ; traceTc "checkingFitsFor }" empty
         ; return (discards, subs) }

    isLocalHoleFit :: HoleFit -> Bool
    isLocalHoleFit hf = case hfElem hf of
                          Just gre -> gre_lcl gre
                          Nothing -> True

    -- See Note [Relevant Constraints]
    relevantCts :: [Ct]
    relevantCts = if isEmptyVarSet (fvVarSet hole_fvs) then []
                  else filter isRelevant simples
      where ctFreeVarSet :: Ct -> VarSet
            ctFreeVarSet = fvVarSet . tyCoFVsOfType . ctPred
            hole_fv_set = fvVarSet hole_fvs
            anyFVMentioned :: Ct -> Bool
            anyFVMentioned ct = not $ isEmptyVarSet $
                                  ctFreeVarSet ct `intersectVarSet` hole_fv_set
            -- We filter out those constraints that have no variables (since
            -- they won't be solved by finding a type for the type variable
            -- representing the hole) and also other holes, since we're not
            -- trying to find hole fits for many holes at once.
            isRelevant ct = not (isEmptyVarSet (ctFreeVarSet ct))
                            && anyFVMentioned ct
                            && not (isHoleCt ct)

    unfoldWrapper :: HsWrapper -> [Type]
    unfoldWrapper = reverse . unfWrp'
      where unfWrp' (WpTyApp ty) = [ty]
            unfWrp' (WpCompose w1 w2) = unfWrp' w1 ++ unfWrp' w2
            unfWrp' _ = []

    -- Takes a list of types and makes sure that the given action
    -- is run with the right TcLevel and restores any Flexi type
    -- variables after the action is run.
    withoutUnification :: FV -> TcM a -> TcM a
    withoutUnification free_vars action
      = do { flexis <- filterM isFlexiTyVar fuvs
           ; result <- setTcLevel deepestFreeTyVarLvl action
             -- Reset any mutated free variables
           ; mapM_ restore flexis
           ; return result }
      where restore = flip writeTcRef Flexi . metaTyVarRef
            fuvs = fvVarList free_vars
            deepestFreeTyVarLvl = foldl' max topTcLevel $ map tcTyVarLevel fuvs

    -- We need to freshen the ev_binds of implications so that we don't have
    -- side effects on them.
    freshenEvBinds :: Implication -> TcM Implication
    freshenEvBinds imp = do { nbinds <- newTcEvBinds
                            ; return imp {ic_binds = nbinds} }

    -- We only clone flexi type variables, and we need to be able to check
    -- whether a variable is filled or not.
    isFlexiTyVar :: TcTyVar -> TcM Bool
    isFlexiTyVar tv | isMetaTyVar tv = isFlexi <$> readMetaTyVar tv
    isFlexiTyVar _ = return False


    -- The real work happens here, where we invoke the type checker using
    -- tcCheckHoleFit to see whether the given type fits the hole.
    fitsHole :: (TcType, [TcTyVar]) -> Type -> TcM (Maybe ([TcType], [TcType]))
    fitsHole (h_ty, ref_vars) ty =
      withoutUnification fvs $
      do { traceTc "checkingFitOf {" $ ppr ty
         ; fresh_implics <- mapM freshenEvBinds implics
         ; (fits, wrp) <-
             tcCheckHoleFit (listToBag relevantCts) fresh_implics h_ty ty
         ; traceTc "Did it fit?" $ ppr fits
         ; traceTc "wrap is: " $ ppr wrp
         ; traceTc "checkingFitOf }" empty
         ; z_wrp_tys <- zonkTcTypes (unfoldWrapper wrp)
         -- We'd like to avoid refinement suggestions like `id _ _` or
         -- `head _ _`, and only suggest refinements where our all phantom
         -- variables got unified during the checking. This can be disabled
         -- with the `-fabstract-refinement-hole-fits` flag.
         ; if fits then fmap ((, ) z_wrp_tys) <$>
           if null ref_vars then return (Just []) else
            do { let -- To be concrete matches, matches have to
                     -- be more than just an invented type variable.
                     fvSet = fvVarSet fvs
                     notAbstract :: TcType -> Bool
                     notAbstract t = case getTyVar_maybe t of
                                       Just tv -> tv `elemVarSet` fvSet
                                       _ -> True
                     allConcrete = all notAbstract z_wrp_tys
                ; z_vars  <- zonkTcTyVars ref_vars
                ; let z_mtvs = mapMaybe tcGetTyVar_maybe z_vars
                ; allFilled <- not <$> anyM isFlexiTyVar z_mtvs
                ; allowAbstract <- goptM Opt_AbstractRefHoleFits
                ; if allowAbstract || (allFilled && allConcrete )
                  then return $ Just z_vars
                  else return Nothing }
            else return Nothing }
     where fvs = mkFVs ref_vars `unionFV` hole_fvs `unionFV` tyCoFVsOfType ty

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
                   ; let zFit = hf {hfType = ty', hfMatches = m', hfWrap = wrp'}
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
            tcSubsumesWCloning ht ty = withoutUnification fvs (tcSubsumes ht ty)
              where fvs = tyCoFVsOfTypes [ht,ty]
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
    go :: Maybe Int -> (TcType, [TcTyVar])
        -> [Either Id GlobalRdrElt] -> TcM (Bool, [HoleFit])
    go = go_ [] emptyVarSet

    -- We iterate over the elements, checking each one in turn for whether it
    -- fits, and adding it to the results if it does.
    go_ :: [HoleFit]           -- What we've found so far.
        -> VarSet              -- Ids we've already checked
        -> Maybe Int           -- How many we're allowed to find, if limited
        -> (TcType, [TcTyVar]) -- The type, and its refinement variables.
        -> [Either Id GlobalRdrElt]     -- The elements we've yet to check.
        -> TcM (Bool, [HoleFit])
    go_ subs _ _ _ [] = return (False, reverse subs)
    go_ subs _ (Just 0) _ _ = return (True, reverse subs)
    go_ subs seen maxleft ty (el:elts) =
      do { traceTc "lookingUp" $ ppr el
         ; maybeThing <- lookup el
         ; case maybeThing of
             Just id | not_trivial id ->
                       do { fits <- fitsHole ty (idType id)
                          ; case fits of
                              Just (wrp, matches) -> keep_it id wrp matches
                              _ -> discard_it }
             _ -> discard_it }
      where discard_it = go_ subs seen maxleft ty elts
            keep_it id wrp ms = go_ (fit:subs) (extendVarSet seen id)
                              ((\n -> n - 1) <$> maxleft) ty elts
              where fit = HoleFit { hfElem = mbel , hfId = id
                                  , hfType = idType id
                                  , hfRefLvl = length (snd ty)
                                  , hfWrap = wrp , hfMatches = ms }
                    mbel = either (const Nothing) Just el
            -- We want to filter out undefined and the likes from GHC.Err
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

-- | Reports whether first type (ty_a) subsumes the second type (ty_b),
-- discarding any errors. Subsumption here means that the ty_b can fit into the
-- ty_a, i.e. `tcSubsumes a b == True` if b is a subtype of a.
tcSubsumes :: TcSigmaType -> TcSigmaType -> TcM Bool
tcSubsumes ty_a ty_b = fst <$> tcCheckHoleFit emptyBag [] ty_a ty_b


-- | A tcSubsumes which takes into account relevant constraints, to fix trac
-- #14273. This makes sure that when checking whether a type fits the hole,
-- the type has to be subsumed by type of the hole as well as fulfill all
-- constraints on the type of the hole.
-- Note: The simplifier may perform unification, so make sure to restore any
-- free type variables to avoid side-effects.
tcCheckHoleFit :: Cts                   -- Any relevant Cts to the hole.
               -> [Implication]         -- The nested implications of the hole
               -> TcSigmaType           -- The type of the hole.
               -> TcSigmaType           -- The type to check whether fits.
               -> TcM (Bool, HsWrapper)
tcCheckHoleFit _ _ hole_ty ty | hole_ty `eqType` ty
    = return (True, idHsWrapper)
tcCheckHoleFit relevantCts implics hole_ty ty = discardErrs $
 do { (wrp, wanted) <- captureConstraints $ tcSubType_NC ExprSigCtxt ty hole_ty
    ; traceTc "Checking hole fit {" empty
    ; traceTc "wanteds are: " $ ppr wanted
    ; let w_rel_cts = addSimples wanted relevantCts
    ; if isEmptyWC w_rel_cts
      then traceTc "}" empty >> return (True, wrp)
      else do { let w_givens = foldl' setWC w_rel_cts implics
              ; traceTc "w_givens are: " $ ppr w_givens
              ; rem <- runTcSDeriveds $ simpl_top w_givens
              -- We don't want any insoluble or simple constraints left, but
              -- solved implications are ok (and neccessary for e.g. undefined)
              ; traceTc "rems was:" $ ppr rem
              ; traceTc "}" empty
              ; return (isSolvedWC rem, wrp) } }
    where
      setWC :: WantedConstraints -> Implication -> WantedConstraints
      setWC wc imp = WC { wc_simple = emptyBag
                        , wc_impl = unitBag $ imp {ic_wanted = wc} }
