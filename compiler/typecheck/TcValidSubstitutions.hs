module TcValidSubstitutions ( findValidSubstitutions ) where

import GhcPrelude

import TcSimplify ( tcCheckHoleFit, tcSubsumes )


import TcRnTypes
import TcRnMonad
import TcMType
import TcType
import Type
import DataCon
import Name
import RdrName ( GlobalRdrEnv, pprNameProvenance
               , GlobalRdrElt (..), globalRdrEnvElts )

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
import FV ( fvVarList, fvVarSet, filterFV )

import Control.Monad    ( filterM, replicateM )
import Data.List        ( partition, sort, foldl' )
import Data.Graph       ( graphFromEdges, topSort )
import Data.Function    ( on )






-- HoleFit is the type we use for a fit in valid substitutions. It contains the
-- element that was checked, the Id of that element as found by `tcLookup`,
-- and the refinement level of the fit, which is the number of extra argument
-- holes that this fit uses (e.g. if hfRefLvl is 2, the fit is for `Id _ _`).
data HoleFit = HoleFit { hfEl :: Maybe GlobalRdrElt -- The element that was
                                                    -- if a global, nothing
                                                    -- if it is a local.
                       , hfId :: Id            -- the elements id in the TcM
                       , hfRefLvl :: Int       -- The number of holes in this fit
                       , hfMatches :: [TcType] } -- What the refinement variables
                                                 -- got matched with, if any.

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
    ppr = pprHoleFit False

-- For pretty printing hole fits, we display the name and type of the fit,
-- with added '_' to represent any extra arguments in case of a non-zero
-- refinement level.
pprHoleFit :: Bool -> HoleFit -> SDoc
pprHoleFit showProv hf =
    if showProv then hang display 2 provenance else display
    where name = case hfEl hf of
                      Just gre -> gre_name gre
                      Nothing -> idName (hfId hf)
          ty = varType (hfId hf)
          matches = hfMatches hf
          holeVs = sep $ map (parens . (text "_" <+> dcolon <+>) . ppr) matches
          idAndTy = pprPrefixOcc name <+> dcolon <+> ppr ty
          display = if null matches
            then idAndTy
            else hang (pprPrefixOcc name <+> holeVs) 2 (text "where" <+> idAndTy)
          provenance = parens $
            case hfEl hf of
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
          TcTvBndr {} -> discard_it
          TcIdBndr id _ -> keep_it id
          TcIdBndr_ExpType name et _ -> discard_it
            -- do { mb_ty <- readExpType_maybe et
            --    ; case mb_ty of
            --        Just ty -> keep_it name ty
            --        Nothing -> discard_it
     where
        discard_it = go env sofar tc_bndrs
        keep_it id = go env (id:sofar) tc_bndrs
          -- = do { (env', ty') <- zonkTidyTcType env ty
          --      ; go env' ((name,ty'):sofar) tc_bndrs }




-- See Note [Valid substitutions include ...]
findValidSubstitutions :: TidyEnv -> [Implication] -> [Ct] -> Ct -> TcM SDoc
findValidSubstitutions tidy_env implics simples ct | isExprHoleCt ct =
  do { rdr_env <- getGlobalRdrEnv
     ; lclBinds <- getLocalBindings tidy_env ct
     ; maxVSubs <- maxValidSubstitutions <$> getDynFlags
     ; showProvenance <- not <$> goptM Opt_UnclutterValidSubstitutions
     ; graphSortSubs <- not <$> goptM Opt_NoSortValidSubstitutions
     ; refLevel <- refLevelSubstitutions <$> getDynFlags
     ; traceTc "findingValidSubstitutionsFor { " $ ppr ct
     ; traceTc "hole_lvl is:" $ ppr hole_lvl
     ; traceTc "implics are: " $ ppr implics
     ; traceTc "simples are: " $ ppr simples
     ; traceTc "locals are: " $ ppr lclBinds
     ; let to_check = map Left lclBinds ++ map Right (globalRdrEnvElts rdr_env)
     ; (searchDiscards, subs) <-
        findSubs graphSortSubs maxVSubs to_check 0 (wrapped_hole_ty, [])
     ; (vDiscards, sortedSubs) <-
        sortSubs graphSortSubs maxVSubs searchDiscards subs
     ; let vMsg = ppUnless (null subs) $
                    hang (text "Valid substitutions include") 2 $
                      vcat (map (pprHoleFit showProvenance) sortedSubs)
                        $$ ppWhen vDiscards subsDiscardMsg
     ; refMsg <- if refLevel >= Just 0 then
         do { maxRSubs <- maxRefSubstitutions <$> getDynFlags
            -- We can use from just, since we know that Nothing >= _ is False.
            ; let refLvls = [1..(fromJust refLevel)]
            -- We make a new refinement type for each level of refinement, where
            -- the level of refinement indicates number of additional arguments
            -- to allow.
            ; ref_tys <- mapM (\l -> (,) l <$> mkRefTy l) refLvls
            ; traceTc "ref_tys are" $ ppr ref_tys
            ; refDs <-
                mapM (uncurry $ findSubs graphSortSubs maxRSubs to_check) ref_tys
            ; (rDiscards, sortedRSubs) <-
                sortSubs graphSortSubs maxRSubs (any fst refDs) $
                    concatMap snd refDs
            ; return $
                ppUnless (null sortedRSubs) $
                  hang (text "Valid refinement substitutions include") 2 $
                  vcat (map (pprHoleFit showProvenance) sortedRSubs)
                    $$ ppWhen rDiscards refSubsDiscardMsg }
       else return empty
     ; traceTc "findingValidSubstitutionsFor }" empty
     ; return (vMsg $$ refMsg)}
  where
    hole_loc = ctEvLoc $ ctEvidence ct
    hole_lvl = ctLocLevel hole_loc
    hole_env = ctLocEnv hole_loc

    -- We make a refinement type by adding a new type variable in front
    -- of the type of t h hole, going from e.g. [Integer] -> Integer
    -- to t_a1/m[tau:1] -> [Integer] -> Integer. This allows the simplifier
    -- to unify the new type variable with any type, allowing us
    -- to suggest a "refinement substitution", like `(foldl1 _)` instead
    -- of only concrete substitutions like `sum`.
    mkRefTy :: Int -> TcM (TcType, [TcType])
    mkRefTy refLvl = (\v -> (wrapHoleWithArgs v, v)) <$> newTyVarTys
     where newTyVarTys = replicateM refLvl $
             setTcLevel hole_lvl newOpenFlexiTyVarTy
           wrapHoleWithArgs args = (wrap_ty . mkFunTys args) hole_ty


    sortSubs :: Bool          -- Whether we should sort the subs or not
                              -- by subsumption or not
             -> Maybe Int     -- How many we should output, if limited.
             -> Bool          -- Whether there were any discards in the
                              -- initial search
             -> [HoleFit]     -- The subs to sort
             -> TcM (Bool, [HoleFit])
    -- If we don't want to sort by the subsumption graph, we just sort it
    -- such that local fits come before global fits, since local fits are
    -- probably more relevant to the user.
    sortSubs False _ discards subs = return (discards, sortedFits)
        where (lclFits, gblFits) = partition isLocalHoleFit subs
              sortedFits = lclFits ++ gblFits
    -- We sort the fits first, to prevent the order of
    -- suggestions being effected when identifiers are moved
    -- around in modules. We use (<*>) to expose the
    -- parallelism, in case it becomes useful later.
    sortSubs _ limit _ subs = possiblyDiscard limit <$>
                                ((++) <$> sortByGraph (sort lclFits)
                                      <*> sortByGraph (sort gblFits))
        where (lclFits, gblFits) = partition isLocalHoleFit subs

    findSubs :: Bool               -- Whether we should sort the subs or not
             -> Maybe Int          -- How many we should output, if limited
             -> [Either Id GlobalRdrElt] -- The elements to check whether fit
             -> Int                -- The refinement level of the hole
             -> (TcType, [TcType]) -- The type to check for fits and ref vars
             -> TcM (Bool, [HoleFit])
    -- We don't check if no output is desired.
    findSubs _ (Just 0) _ _ _ = return (False, [])
    findSubs sortSubs maxSubs to_check refLvl ht@(hole_ty, _) =
      do { traceTc "checkingSubstitutionsFor {" $ ppr hole_ty
         ; let limit = if sortSubs then Nothing else maxSubs
         ; (discards, subs) <- setTcLevel hole_lvl $
                                 go limit ht refLvl to_check
         ; traceTc "}" empty
         ; return (discards, subs) }
    -- We extract the type of the hole from the constraint.
    hole_ty :: TcPredType
    hole_ty = ctPred ct
    hole_fvs = tyCoFVsOfType hole_ty

    -- For checking, we wrap the type of the hole with all the givens
    -- from all the implications in the context.
    wrap_ty :: TcType -> TcSigmaType
    wrap_ty ty = foldl' w_ty ty implics
        where w_ty ty impl = mkFunTys (map idType (ic_given impl)) ty

    wrapped_hole_ty :: TcSigmaType
    wrapped_hole_ty = wrap_ty hole_ty

    isLocalHoleFit :: HoleFit -> Bool
    isLocalHoleFit hf = case hfEl hf of
                          Just gre -> gre_lcl gre
                          Nothing -> True

    -- We rearrange the elements to make locals appear at the top of the list
    -- since they're most likely to be relevant to the user.
    localsFirst :: [HoleFit] -> [HoleFit]
    localsFirst elts = lcl ++ gbl
      where (lcl, gbl) = partition isLocalHoleFit elts


    -- These are the constraints whose every free unification variable is
    -- mentioned in the type of the hole.
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
    getHoleCloningSubst :: [TcType] -> TcM TCvSubst
    getHoleCloningSubst tys = mkTvSubstPrs <$> getClonedVars
      where cloneFV :: TyVar -> TcM (Maybe (TyVar, Type))
            cloneFV fv | tvl >= hole_lvl
              = fmap Just $
                  ((,) fv) <$> (setTcLevel (pushTcLevel tvl) (newFlexiTyVarTy (varType fv)))
              where tvl = tcTyVarLevel fv
            cloneFV _ = return Nothing
            -- The subsumption check pushes the level, so as to be sure that
            -- its invocation of the solver doesn't unify type variables floating
            -- about that are unrelated to the subsumption check. However, these
            -- cloned variables in the hole type *should* be unified, so we make
            -- sure to bump the level before creating them
            getClonedVars :: TcM [(TyVar, Type)]
            getClonedVars = mapMaybeM cloneFV (fvVarList $ tyCoFVsOfTypes tys)
            -- cloneFV :: TyVar -> TcM (TyVar, Type)
            -- cloneFV fv | isTouchableMetaTyVar hole_lvl fv
            --   = (,) fv <$> (mkTyVarTy <$> cloneMetaTyVar fv)
            -- cloneFV fv = (,) fv <$> newMetaTyVarTyAtLevel hole_lvl (varType fv)



    -- This applies the given substitution to the given constraint.
    applySubToCt :: TCvSubst -> Ct -> Ct
    applySubToCt sub ct = ct {cc_ev = ev {ctev_pred = subbedPredType} }
      where subbedPredType = substTy sub $ ctPred ct
            ev = ctEvidence ct

    applyCloning :: (TcType, [TcType])
                 -> Type
                 -> [Ct]
                 -> TcM (TcType, [TcType], Type, [Ct])
    applyCloning (hole_ty, vars) typ cts
     = do { cloneSub <- getHoleCloningSubst [hole_ty, typ]
          ; let cHoleTy = substTy cloneSub hole_ty
                cCts = map (applySubToCt cloneSub) cts
                cVars = map (substTy cloneSub) vars
                cTy = substTy cloneSub typ

          -- ; tidy_cHoleTy <- zonkTcType cHoleTy
          -- ; tidy_cTy <- zonkTcType cTy
          ; return (cHoleTy, cVars, cTy, cCts)
          }
    -- The real work happens here, where we invoke the type checker
    -- to check whether we the given type fits into the hole!
    -- To check: Clone all relevant cts and the hole
    -- then solve the subsumption check AND check that all other
    -- the other constraints were solved.
    fitsHole :: (TcType, [TcType]) -> Type -> TcM (Maybe [TcType])
    fitsHole hole_ty typ =
      do { traceTc "checkingFitOf {" $ ppr typ
         ; traceTc "tys before are: " $ ppr (hole_ty, typ)
         ; traceTc "fvs are" $ ppr $ (fvVarList $ tyCoFVsOfTypes [fst hole_ty, typ])
         ; (cHoleTy, cVars, cTy, cCts) <- applyCloning hole_ty typ relevantCts
         ; absFits <- tcCheckHoleFit (listToBag cCts) cVars cHoleTy cTy
         ; traceTc "Did it fit?" $ ppr absFits
         ; traceTc "tys after are: " $ ppr (cHoleTy, cTy)
         ; traceTc "}" empty
         -- We'd like to avoid refinement suggestions like `id _ _` or
         -- `head _ _`, and only suggest refinements where our all phantom
         -- variables got unified during the checking. This can be disabled
         -- with the `-fabstract-refinement-substitutions` flag.
         ; if absFits then
           if null cVars then return (Just []) else
            do { let mtvs :: [TyVar]
                     mtvs = mapMaybe tcGetTyVar_maybe cVars
                     getMTy :: MetaDetails -> Maybe TcType
                     getMTy Flexi = Nothing
                     getMTy (Indirect t) = Just t
                ; matches <- mapM (fmap getMTy . readMetaTyVar) mtvs
                ; allFilled <- goptM Opt_AbstractRefSubstitutions `orM`
                               return (all isJust matches)
                ; if allFilled then return (Just (catMaybes matches))
                  else return Nothing }
            else return Nothing }

    -- Based on the flags, we might possibly discard some or all the
    -- fits we've found.
    possiblyDiscard :: Maybe Int -> [HoleFit] -> (Bool, [HoleFit])
    possiblyDiscard (Just max) fits = (fits `lengthExceeds` max, take max fits)
    possiblyDiscard Nothing fits = (False, fits)

    -- Based on a suggestion by phadej on #ghc, we can sort the found fits
    -- by constructing a subsumption graph, and then do a topological sort of
    -- the graph. This makes the most specific types appear first, which are
    -- probably those most relevant. This takes a lot of work (but results in
    -- much more useful output), and can be disabled by
    -- '-fno-sort-valid-substitutions'.
    sortByGraph :: [HoleFit] -> TcM [HoleFit]
    sortByGraph fits = go [] fits
      where hfType :: HoleFit -> TcSigmaType
            hfType = varType . hfId

            tcSubsumesWCloning :: TcType -> TcType -> TcM Bool
            tcSubsumesWCloning ht ty =
              do { (cht, _, cty, _) <- applyCloning (ht, []) ty []
                 ; setTcLevel hole_lvl $ tcSubsumes cht cty }
            go :: [(HoleFit, [HoleFit])] -> [HoleFit] -> TcM [HoleFit]
            go sofar [] = do { traceTc "subsumptionGraph was" $ ppr sofar
                             ; return $ localsFirst topSorted }
              where toV (hf, adjs) = (hf, hfId hf, map hfId adjs)
                    (graph, fromV, _) = graphFromEdges $ map toV sofar
                    topSorted = map ((\(h,_,_) -> h) . fromV) $ topSort graph
            go sofar (id:ids) =
              do { adjs <- filterM (tcSubsumesWCloning (hfType id) . hfType) fits
                 ; go ((id, adjs):sofar) ids }

    -- Kickoff the checking of the elements.
    go :: Maybe Int -> (TcType, [TcType]) -> Int
        -> [Either Id GlobalRdrElt] -> TcM (Bool, [HoleFit])
    go = go_ [] emptyVarSet

    -- We use this when checking against global matches,
    -- where we want the refinement variables to be free
    -- to unify with anything, but we want to hide
    -- any local variables of the types.
    -- wrapNonRefinementVariables :: (TcType, [TcType]) -> (TcType, [TcType])
    -- wrapNonRefinementVariables (t, refvs) = (mkSpecForAllTys skols t, refvs)
    --   where
    --     skols =
    --       fvVarList $ filterFV (not . flip elemVarSet rtyvs) $ tyCoFVsOfType t
    --     rtyvs = fvVarSet (tyCoFVsOfTypes refvs)

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
    go_ subs seen maxleft t r (el:elts) =
      do { traceTc "lookingUp" $ ppr el
         ; let ty_to_check = t -- case el of
                                    -- Left _ -> t
                                    -- Right _ -> wrapNonRefinementVariables t
         ; maybeThing <- lookup el
         ; case maybeThing of
             Just id | (not_trivial id && not (id `elemVarSet` seen)) ->
                       do { fits <- fitsHole ty_to_check (idType id)
                          ; case fits of
                              Just matches -> keep_it id
                                              (HoleFit
                                               (either (const Nothing) Just el)
                                               id r matches)
                              _ -> discard_it }
             _ -> discard_it }
      where discard_it = go_ subs seen maxleft t r elts
            keep_it id fit =
              go_ (fit:subs) (extendVarSet seen id)
                  ((\n -> n - 1) <$> maxleft) t r elts
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
findValidSubstitutions _ _ _ _ = return empty

subsDiscardMsg :: SDoc
subsDiscardMsg =
    text "(Some substitutions suppressed;" <+>
    text "use -fmax-valid-substitutions=N or -fno-max-valid-substitutions)"

refSubsDiscardMsg :: SDoc
refSubsDiscardMsg =
    text "(Some refinement substitutions suppressed;" <+>
    text "use -fmax-refinement-substitutions=N" <+>
    text "or -fno-max-refinement-substitutions)"


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
        (imported from ‘Prelude’ at test.hs:1:8-11
         (and originally defined in ‘base-4.11.0.0:Data.OldList’))
      words :: String -> [String]
        (imported from ‘Prelude’ at test.hs:1:8-11
         (and originally defined in ‘base-4.11.0.0:Data.OldList’))
      read :: forall a. Read a => String -> a
        (imported from ‘Prelude’ at test.hs:1:8-11
         (and originally defined in ‘Text.Read’))
      inits :: forall a. [a] -> [[a]]
        (imported from ‘Data.List’ at test.hs:3:19-23
         (and originally defined in ‘base-4.11.0.0:Data.OldList’))
      repeat :: forall a. a -> [a]
        (imported from ‘Prelude’ at test.hs:1:8-11
         (and originally defined in ‘GHC.List’))
      mempty :: forall a. Monoid a => a
        (imported from ‘Prelude’ at test.hs:1:8-11
         (and originally defined in ‘GHC.Base’))
      return :: forall (m :: * -> *). Monad m => forall a. a -> m a
        (imported from ‘Prelude’ at test.hs:1:8-11
         (and originally defined in ‘GHC.Base’))
      pure :: forall (f :: * -> *). Applicative f => forall a. a -> f a
        (imported from ‘Prelude’ at test.hs:1:8-11
         (and originally defined in ‘GHC.Base’))
      fail :: forall (m :: * -> *). Monad m => forall a. String -> m a
        (imported from ‘Prelude’ at test.hs:1:8-11
         (and originally defined in ‘GHC.Base’))
      error :: forall (a :: TYPE r). GHC.Stack.Types.HasCallStack => [Char] -> a
        (imported from ‘Prelude’ at test.hs:1:8-11
         (and originally defined in ‘GHC.Err’))
      errorWithoutStackTrace :: forall (a :: TYPE r). [Char] -> a
        (imported from ‘Prelude’ at test.hs:1:8-11
         (and originally defined in ‘GHC.Err’))
      undefined :: forall (a :: TYPE r). GHC.Stack.Types.HasCallStack => a
        (imported from ‘Prelude’ at test.hs:1:8-11
         (and originally defined in ‘GHC.Err’))


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
affecting the hole and later checks. When outputting, take the fits found for
the hole and build a subsumption graph, where fit a and fit b are connected if
a subsumes b. We then sort the graph topologically, and output the suggestions
in that order. This is done in order to display "more relevant" suggestions
first where the most specific suggestions (i.e. the ones that are subsumed by
the other suggestions) appear first. This puts suggestions such as `error` and
`undefined` last, as seen in the example above.

When the flag `-frefinement-level-substitutions=n` where `n > 0` is passed, we
also look for valid refinement substitutions, i.e. substitutions that are valid,
but adds more holes. Consider the following:

  f :: [Integer] -> Integer
  f = _

Here the valid substitutions suggested will be (with the
`-funclutter-valid-substitutions` flag set):

  Valid substitutions include
    f :: [Integer] -> Integer
    product :: forall (t :: * -> *).
              Foldable t => forall a. Num a => t a -> a
    sum :: forall (t :: * -> *).
          Foldable t => forall a. Num a => t a -> a
    maximum :: forall (t :: * -> *).
              Foldable t => forall a. Ord a => t a -> a
    minimum :: forall (t :: * -> *).
              Foldable t => forall a. Ord a => t a -> a
    head :: forall a. [a] -> a
    (Some substitutions suppressed;
        use -fmax-valid-substitutions=N or -fno-max-valid-substitutions)

When the `-frefinement-level-substitutions=1` flag is given, we additionally
compute and report valid refinement substitutions:

  Valid refinement substitutions include
    foldl1 _ :: forall (t :: * -> *).
                Foldable t => forall a. (a -> a -> a) -> t a -> a
    foldr1 _ :: forall (t :: * -> *).
                Foldable t => forall a. (a -> a -> a) -> t a -> a
    head _ :: forall a. [a] -> a
    last _ :: forall a. [a] -> a
    error _ :: forall (a :: TYPE r).
                GHC.Stack.Types.HasCallStack => [Char] -> a
    errorWithoutStackTrace _ :: forall (a :: TYPE r). [Char] -> a
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
