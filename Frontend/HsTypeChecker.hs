{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Frontend.HsTypeChecker (hsElaborate) where

import Frontend.HsTypes
import Frontend.HsRenamer

import Backend.FcTypes

import Utils.Substitution
import Utils.FreeVars
import Utils.Var
import Utils.Kind
import Utils.Unique
import Utils.AssocList
import Utils.Annotated
import Utils.Ctx
import Utils.PrettyPrint hiding ((<>))
import Utils.Utils
import Utils.Errors
import Utils.SnocList

import Control.Monad.Writer hiding((<>))
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Fail
import Control.Arrow (second)
import Data.List (nub)
import Data.Maybe (catMaybes)
import Data.Semigroup

-- * Create the typechecking environment from the renaming one
-- ------------------------------------------------------------------------------

-- | Build the initial typechecker environment from the renaming environment
buildInitTcEnv :: RnProgram -> RnEnv -> TcM ()
buildInitTcEnv pgm (RnEnv _rn_cls_infos dc_infos tc_infos) = do -- Assume that the initial environment is completely empty (mempty mempty mempty)
  -- Prepopulate the environment with the (user-defined) data constructor information
  mapAssocListM_ (uncurry addDataConInfoTcM) $
    mapFstWithDataAssocList (\_ info -> hs_dc_data_con info) dc_infos
  -- Prepopulate the environment with the (user-defined) type constructor information
  mapAssocListM_ (uncurry addTyConInfoTcM)   $
    mapFstWithDataAssocList (\_ info -> hs_tc_ty_con   info) tc_infos
  -- Create and store in the environment all infos for type classes
  -- (and the constructors they give rise to) -- UPDATE THIS WHEN YOU ADD SUPERCLASSES
  buildStoreClsInfos pgm
  where
    buildStoreClsInfos :: RnProgram -> TcM ()
    buildStoreClsInfos (PgmExp {})   = return ()
    buildStoreClsInfos (PgmInst _ p) = buildStoreClsInfos p
    buildStoreClsInfos (PgmData _ p) = buildStoreClsInfos p
    buildStoreClsInfos (PgmVal  _ p) = buildStoreClsInfos p
    buildStoreClsInfos (PgmCls  c p) = case c of
      ClsD rn_cs rn_cls (rn_a :| _kind) rn_method method_ty -> do
        -- Generate And Store The TyCon Info
        fc_tc <- FcTC . mkName (mkSym ("T" ++ (show $ symOf rn_cls))) <$> getUniqueM

        -- Generate And Store The DataCon Info
        fc_dc  <- FcDC . mkName (mkSym ("K" ++ (show $ symOf rn_cls))) <$> getUniqueM

        fc_fam <- FcTF . mkName (mkSym ("F" ++ (show $ symOf rn_cls))) <$> getUniqueM

        -- Generate And Store The Class Info
        let cls_info = ClassInfo rn_cs rn_cls [rn_a] rn_method method_ty fc_tc fc_dc fc_fam
        addClsInfoTcM rn_cls cls_info

        -- Continue with the rest
        buildStoreClsInfos p

-- | Add a renamed class name to the state
addClsInfoTcM :: RnClass -> ClassInfo -> TcM ()
addClsInfoTcM cls info = modify $ \s ->
  s { tc_env_cls_info = extendAssocList cls info (tc_env_cls_info s) }

-- | Add a renamed datacon name to the state
addDataConInfoTcM :: RnDataCon -> HsDataConInfo -> TcM ()
addDataConInfoTcM dc info = modify $ \s ->
  s { tc_env_dc_info = extendAssocList dc info (tc_env_dc_info s) }

-- | Add a renamed tycon name to the state
addTyConInfoTcM :: RnTyCon -> HsTyConInfo -> TcM ()
addTyConInfoTcM tc info = modify $ \s ->
  s { tc_env_tc_info = extendAssocList tc info (tc_env_tc_info s) }

-- * Type Checking Monad
-- ------------------------------------------------------------------------------

type TcM = UniqueSupplyT (ReaderT TcCtx (StateT TcEnv (Except CompileError)))

data TcEnv = TcEnv { tc_env_cls_info :: AssocList RnClass   ClassInfo
                   , tc_env_dc_info  :: AssocList RnDataCon HsDataConInfo
                   , tc_env_tc_info  :: AssocList RnTyCon   HsTyConInfo
                   , tc_env_tuples   :: AssocList Int       (FcTyCon, FcDataCon)
                   }

instance PrettyPrint TcEnv where
  ppr (TcEnv cls_infos dc_infos tc_infos fc_tuples)
    = braces $ vcat $ punctuate comma
    [ text "tc_env_cls_info" <+> colon <+> ppr cls_infos
    , text "tc_env_dc_info"  <+> colon <+> ppr dc_infos
    , text "tc_env_tc_info"  <+> colon <+> ppr tc_infos
    , text "tc_env_tuples"   <+> colon <+> ppr fc_tuples
    ]
  needsParens _ = False

-- * Lookup data and type constructors for a class
-- ------------------------------------------------------------------------------

-- 1. Rename TcEnv to TcGblEnv
-- 2. It's exactly the same as lookupFcGblEnv. Abstract over both.

-- | Lookup something in the global environment
lookupTcEnvM ::  (Eq a, PrettyPrint a, MonadError CompileError m, MonadState s m) => (s -> AssocList a b) -> a -> m b
lookupTcEnvM f x = gets f >>= \l -> case lookupInAssocList x l of
  Just y  -> return y
  Nothing -> tcFail (text "lookupTcEnvM" <+> colon <+> ppr x <+> text "is unbound")

-- | Lookup a type constructor
lookupTyCon :: RnTyCon -> TcM FcTyCon
lookupTyCon tc = hs_tc_fc_ty_con <$> lookupTcEnvM tc_env_tc_info tc

-- | Lookup the kind of a type constructor
tyConKind :: RnTyCon -> TcM Kind
tyConKind tc = do
  info <- lookupTcEnvM tc_env_tc_info tc
  return (mkArrowKind (map kindOf (hs_tc_type_args info)) KStar)

-- | Lookup a data constructor
lookupDataCon :: RnDataCon -> TcM FcDataCon
lookupDataCon dc = hs_dc_fc_data_con <$> lookupTcEnvM tc_env_dc_info dc

-- | Lookup the kinds of the arguments
clsArgKinds :: RnClass -> TcM [Kind]
clsArgKinds cls = map kindOf . cls_type_args <$> lookupTcEnvM tc_env_cls_info cls

-- | Lookup the System Fc type constructor for a class
lookupClsTyCon :: RnClass -> TcM FcTyCon
lookupClsTyCon cls = cls_tycon <$> lookupTcEnvM tc_env_cls_info cls

-- | Lookup the System Fc data constructor for a class
lookupClsDataCon :: RnClass -> TcM FcDataCon
lookupClsDataCon cls = cls_datacon <$> lookupTcEnvM tc_env_cls_info cls

-- | Lookup the System Fc type family for a class
lookupClsTyFam :: RnClass -> TcM FcTyFam
lookupClsTyFam cls = cls_tyfam <$> lookupTcEnvM tc_env_cls_info cls

-- | Lookup the type class method name
lookupClsMethod :: RnClass -> TcM RnTmVar
lookupClsMethod cls = cls_method <$> lookupTcEnvM tc_env_cls_info cls

-- | Get the signature of a data constructor in pieces
dataConSig :: RnDataCon -> TcM ([RnTyVar], [RnMonoTy], RnTyCon)
dataConSig dc = lookupTcEnvM tc_env_dc_info dc >>= \info ->
  return ( hs_dc_univ    info
         , hs_dc_arg_tys info
         , hs_dc_parent  info )

-- | Get the superclasses of a class
lookupClsSuper :: RnClass -> TcM RnClsCs
lookupClsSuper cls = cls_super <$> lookupTcEnvM tc_env_cls_info cls

-- | Get the parameter of the class
lookupClsParam :: RnClass -> TcM RnTyVar
lookupClsParam cls = do
  info <- lookupTcEnvM tc_env_cls_info cls
  case cls_type_args info of
    [a] -> return a
    _   -> tcFail (text "lookupClsParam")

-- | Get the type constructor and data constructor for a tuple with the given
-- arity. Tuples that aren't in the environment will be lazely created.
lookupFcTuple :: Int -> TcM (FcTyCon, FcDataCon)
lookupFcTuple arity = lookupTcEnvM tc_env_tuples arity `catchError` \_ -> do
  fc_tc  <- FcTC . mkName (mkSym "Tuple#") <$> getUniqueM
  fc_dc  <- FcDC . mkName (mkSym "Tuple#") <$> getUniqueM
  modify $ \s ->
    s { tc_env_tuples = extendAssocList arity (fc_tc, fc_dc) (tc_env_tuples s) }
  return (fc_tc, fc_dc)

-- * Type and Constraint Elaboration (With Well-formedness (well-scopedness) Check)
-- ------------------------------------------------------------------------------

-- | Elaborate a monotype
wfElabMonoTy :: RnMonoTy -> TcM (Kind, FcType)
wfElabMonoTy (TyCon tc) = do
  kind  <- tyConKind tc
  fc_tc <- lookupTyCon tc
  return (kind, FcTyCon fc_tc)
wfElabMonoTy (TyApp ty1 ty2) = do
  (k1, fc_ty1) <- wfElabMonoTy ty1
  (k2, fc_ty2) <- wfElabMonoTy ty2
  case k1 of
    KArr k1a k1b
      | k1a == k2 -> return (k1b, FcTyApp fc_ty1 fc_ty2)
    _other_kind   -> tcFail (text "wfElabMonoTy" <+> colon <+> text "TyApp")
wfElabMonoTy (TyVar v) = do
  kind <- lookupCtxM v
  return (kind, rnTyVarToFcType v)

-- | Elaborate a qualified type
wfElabQualTy :: RnQualTy -> TcM (Kind, FcType)
wfElabQualTy (QMono ty)    = wfElabMonoTy ty
wfElabQualTy (QQual ct ty) = do
  fc_ty1         <- wfElabClsCt ct
  (kind, fc_ty2) <- wfElabQualTy ty
  unless (kind == KStar) $
    tcFail (text "wfElabQualTy" <+> colon <+> text "QQual")
  return (KStar, mkFcArrowTy fc_ty1 fc_ty2)

-- | Elaborate a constraint
wfElabClsCt :: RnClsCt -> TcM FcType
wfElabClsCt (ClsCt cls ty) = do
  (ty_kind, fc_ty) <- wfElabMonoTy ty
  clsArgKinds cls >>= \case
    [k] | k == ty_kind -> do
      fc_tc <- lookupClsTyCon cls
      return (FcTyApp (FcTyCon fc_tc) fc_ty)
    _other_kind -> tcFail (text "wfElabClsCt")

-- | Elaborate a list of constraints
wfElabClsCs :: RnClsCs -> TcM [FcType]
wfElabClsCs = mapM wfElabClsCt

-- | Elaborate a polytype
wfElabPolyTy :: RnPolyTy -> TcM (Kind, FcType)
wfElabPolyTy (PQual ty) = wfElabQualTy ty
wfElabPolyTy (PPoly (a :| _) ty) = do
  notInCtxM a {- ensure is unbound -}
  (kind, fc_ty) <- extendCtxM a (kindOf a) (wfElabPolyTy ty)
  unless (kind == KStar) $
    tcFail (text "wfElabPolyTy" <+> colon <+> text "PPoly")
  return (KStar, FcTyAbs (rnTyVarToFcTyVar a) fc_ty)

-- * Type and Constraint Elaboration (Without Well-scopedness Check)
-- ------------------------------------------------------------------------------

-- | Elaborate a monotype
elabMonoTy :: RnMonoTy -> TcM FcType
elabMonoTy (TyCon tc)      = FcTyCon <$> lookupTyCon tc
elabMonoTy (TyApp ty1 ty2) = FcTyApp <$> elabMonoTy ty1 <*> elabMonoTy ty2
elabMonoTy (TyVar v)       = return (rnTyVarToFcType v)

-- | Elaborate a class constaint
elabClsCt :: RnClsCt -> TcM FcType
elabClsCt (ClsCt cls ty) =
  FcTyApp <$> (FcTyCon <$> lookupClsTyCon cls) <*> elabMonoTy ty

-- | Elaborate a class constaint scheme
elabScheme :: CtrScheme -> TcM FcType
elabScheme (CtrScheme as cs cls_ct) = elabAbs as $ elabImpls cs $ elabClsCt cls_ct
  where
    elabImpls (ct1:cs') fc = mkFcArrowTy <$> elabClsCt ct1 <*> elabImpls cs' fc
    elabImpls [] fc = fc
    elabAbs ((a :| _):as') fc = FcTyAbs (rnTyVarToFcTyVar a) <$> elabAbs as' fc
    elabAbs [] fc = fc

-- | Elaborate a polytype
elabPolyTy :: RnPolyTy -> TcM FcType
elabPolyTy (PQual ty) = elabQualTy ty
elabPolyTy (PPoly (a :| _) ty) =
  FcTyAbs (rnTyVarToFcTyVar a) <$> elabPolyTy ty

-- | Elaborate a qualified type
elabQualTy :: RnQualTy -> TcM FcType
elabQualTy (QQual cls_ct ty) =
  mkFcArrowTy <$> elabClsCt cls_ct <*> elabQualTy ty
elabQualTy (QMono ty) = elabMonoTy ty

-- * Constraint store
-- ------------------------------------------------------------------------------

-- | ConstraintStore containing both the equality constraints and named class constraints
data ConstraintStore = CS EqCs AnnClsCs

instance Semigroup ConstraintStore where
  (<>) = mappend

instance Monoid ConstraintStore where
  mempty = CS mempty mempty
  mappend (CS eqs1 ccs1) (CS eqs2 ccs2)
    = CS (mappend eqs1 eqs2) (mappend ccs1 ccs2)

-- | Type inference generation monad
newtype GenM a = GenM (StateT ConstraintStore TcM a)
  deriving ( Functor, Applicative, Monad
           , MonadState ConstraintStore, MonadReader TcCtx, MonadError CompileError)

-- All this is bad. We should not store the unique supply within the
-- global environment, rather wrap our monads with the UniqueSupplyT transformer
instance MonadUnique GenM where
  getUniqueSupplyM = liftGenM getUniqueSupplyM

-- | Get out of the constraint generation monad
runGenM :: GenM a -> TcM (a, EqCs, AnnClsCs)
runGenM (GenM m) = do
    (v , (CS eqs ccs)) <- runStateT m mempty
    return (v, eqs, ccs)

-- | Lift TcM into GenM
liftGenM :: TcM a -> GenM a
liftGenM m = GenM (StateT (\cs -> m >>= \x -> return (x, cs)))

-- | Add some equality constraints in the constraint store
storeEqCs :: EqCs -> GenM ()
storeEqCs cs = modify (\(CS eqs ccs) -> CS (cs ++ eqs) ccs)

-- | Add some (variable-annotated) class constraints in the constraint store
storeAnnCts :: AnnClsCs -> GenM ()
storeAnnCts cs = modify (\(CS eqs ccs) -> CS eqs (mappend ccs cs))

-- | Add many type variables to the typing context
extendTcCtxTysM :: MonadReader TcCtx m => [RnTyVar] -> m a -> m a
extendTcCtxTysM []     m = m
extendTcCtxTysM ty_vars m = foldl (\m' a -> extendCtxM a (kindOf a) m') m ty_vars

-- | Set the typing environment
setTcCtxTmM :: MonadReader TcCtx m => TcCtx -> m a -> m a
setTcCtxTmM ctx = local (\_ -> ctx)

-- * Term Elaboration
-- ------------------------------------------------------------------------------

-- | Freshen up a list of type variables. Return
--   a) the list of fresh variables (NB: same length as input)
--   b) the substitution from the old to the fresh ones
freshenRnTyVars :: [RnTyVar] -> TcM ([RnTyVar], HsTySubst)
freshenRnTyVars tvs = do
  new_tvs <- mapM freshRnTyVar (map kindOf tvs)
  let subst = buildRnSubst (zipExact tvs new_tvs)
  return (new_tvs, subst)

-- | Instantiate a polytype with fresh unification variables
instPolyTy :: RnPolyTy -> TcM ([RnTyVar], RnClsCs, RnMonoTy)
instPolyTy poly_ty = do
  (bs,subst) <- freshenRnTyVars (map labelOf as)
  let new_cs = substInClsCs subst cs
  let new_ty = substInMonoTy subst ty
  return (bs, new_cs, new_ty)
  where
    (as, cs, ty) = destructPolyTy poly_ty

-- | Generate a number of fresh dictionary variables
genFreshDictVars :: MonadUnique m => Int -> m [DictVar]
genFreshDictVars n = replicateM n freshDictVar

-- | Annotate a list of constraints with a fresh dictionary variables
annotateCts :: RnClsCs -> TcM ([DictVar], AnnClsCs)
annotateCts cs = do
  ds <- genFreshDictVars (length cs)
  return (ds, (ds) |: (cs))

-- | Elaborate a term
elabTerm :: RnTerm -> GenM (RnMonoTy, FcTerm)
elabTerm (TmApp tm1 tm2)   = elabTmApp tm1 tm2
elabTerm (TmAbs x tm)      = elabTmAbs x tm
elabTerm (TmVar x)         = elabTmVar x
elabTerm (TmCon dc)        = liftGenM (elabTmCon dc)
elabTerm (TmLet x tm1 tm2) = elabTmLet x tm1 tm2
elabTerm (TmCase scr alts) = elabTmCase scr alts

-- | Elaborate a term application
elabTmApp :: RnTerm -> RnTerm -> GenM (RnMonoTy, FcTerm)
elabTmApp tm1 tm2 = do
  (ty1, fc_tm1) <- elabTerm tm1
  (ty2, fc_tm2) <- elabTerm tm2
  a <- TyVar <$> freshRnTyVar KStar
  storeEqCs [mkRnArrowTy [ty2] a :~: ty1]
  return (a, FcTmApp fc_tm1 fc_tm2)

-- | Elaborate a lambda abstraction
elabTmAbs :: RnTmVar -> RnTerm -> GenM (RnMonoTy, FcTerm)
elabTmAbs x tm = do
  liftGenM (notInCtxM x) {- ensure not bound -}
  tv <- freshRnTyVar KStar
  (ty, fc_tm) <- extendCtxM x (monoTyToPolyTy (TyVar tv)) $ elabTerm tm
  let result = FcTmAbs (rnTmVarToFcTmVar x) (rnTyVarToFcType tv) fc_tm
  return (mkRnArrowTy [TyVar tv] ty, result)

-- | Elaborate a term variable
elabTmVar :: RnTmVar -> GenM (RnMonoTy, FcTerm)
elabTmVar x = do
  poly_ty     <- liftGenM (lookupCtxM x)
  (bs,cs,ty)  <- liftGenM (instPolyTy poly_ty)
  _           <- extendTcCtxTysM bs $ liftGenM (wfElabClsCs cs)
  (ds,ann_cs) <- liftGenM (annotateCts cs)
  storeAnnCts ann_cs -- store the constraints
  let fc_ds = map FcTmVar ds         -- System F representation
  let fc_bs = map rnTyVarToFcType bs -- System F representation
  let fc_tm = fcTmApp (fcTmTyApp (rnTmVarToFcTerm x) fc_bs) fc_ds
  return (ty, fc_tm)

-- | Elaborate a let binding (monomorphic, recursive)
elabTmLet :: RnTmVar -> RnTerm -> RnTerm -> GenM (RnMonoTy, FcTerm)
elabTmLet x tm1 tm2 = do
  liftGenM (notInCtxM x) {- ensure not bound -}
  tv <- freshRnTyVar KStar
  (ty1, fc_tm1) <- extendCtxM x (monoTyToPolyTy (TyVar tv)) $ elabTerm tm1
  (ty2, fc_tm2) <- extendCtxM x (monoTyToPolyTy (TyVar tv)) $ elabTerm tm2 -- could have also passed ty1 but it is the same
  storeEqCs [TyVar tv :~: ty1]
  let fc_tm = FcTmLet (rnTmVarToFcTmVar x) (rnTyVarToFcType tv) fc_tm1 fc_tm2
  return (ty2, fc_tm)

-- | Elaborate a data constructor
elabTmCon :: RnDataCon -> TcM (RnMonoTy, FcTerm)
elabTmCon dc = do
  (bs, arg_tys, tc) <- freshenDataConSig dc
  fc_dc <- lookupDataCon dc

  let mono_ty = mkRnArrowTy arg_tys (mkTyConApp tc (map TyVar bs))                 -- Haskell monotype
  let fc_tm = fcTmTyApp (FcTmDataCon fc_dc) (rnTyVarsToFcTypes bs) -- System F term

  return (mono_ty, fc_tm)

freshenDataConSig :: RnDataCon -> TcM ([RnTyVar], [RnMonoTy], RnTyCon)
freshenDataConSig dc = do
  (as, arg_tys, tc) <- dataConSig dc
  (bs, subst) <- freshenRnTyVars as                              -- Freshen up the universal type variables
  return (bs, substInMonoTy subst <$> arg_tys, tc)

-- | Elaborate a case expression
elabTmCase :: RnTerm -> [RnAlt] -> GenM (RnMonoTy, FcTerm)
elabTmCase scr alts = do
  (scr_ty, fc_scr) <- elabTerm scr               -- Elaborate the scrutinee
  rhs_ty  <- TyVar <$> freshRnTyVar KStar        -- Generate a fresh type variable for the result
  fc_alts <- mapM (elabHsAlt scr_ty rhs_ty) alts -- Check the alternatives
  return (rhs_ty, FcTmCase fc_scr fc_alts)

-- | Elaborate a case alternative
elabHsAlt :: RnMonoTy {- Type of the scrutinee -}
          -> RnMonoTy {- Result type           -}
          -> RnAlt    {- Case alternative      -}
          -> GenM FcAlt
elabHsAlt scr_ty res_ty (HsAlt (HsPat dc xs) rhs) = do
  -- Get the constructor's signature
  (as, orig_arg_tys, tc) <- liftGenM (dataConSig dc)
  -- Get the constructor's System F representation
  fc_dc <- liftGenM (lookupDataCon dc)

  -- Generate fresh universal type variables for the universal tvs
  (bs, ty_subst) <- liftGenM (freshenRnTyVars as)
  -- Apply the renaming substitution to the argument types
  let arg_tys = substInMonoTy ty_subst <$> orig_arg_tys
  -- Type check the right hand side
  (rhs_ty, fc_rhs) <- extendCtxM xs (monoTyToPolyTy <$> arg_tys) (elabTerm rhs)
  -- The scrutinee type must match the pattern type
  storeEqCs [ scr_ty :~: foldl TyApp (TyCon tc) (map TyVar bs)
            -- All right hand sides should be the same
            , res_ty :~: rhs_ty ]

  fc_tys <- liftGenM $ mapM elabMonoTy arg_tys
  return (FcAlt (FcConPat fc_dc [] [] ((rnTmVarToFcTmVar <$> xs) |: fc_tys)) fc_rhs)

-- | Covert a renamed type variable to a System F type
rnTyVarToFcType :: RnTyVar -> FcType
rnTyVarToFcType = FcTyVar . rnTyVarToFcTyVar

-- | Covert a list of renamed type variables to a list of System F types
rnTyVarsToFcTypes :: [RnTyVar] -> [FcType]
rnTyVarsToFcTypes = map rnTyVarToFcType

-- | Covert a renamed term variable to a System F term
rnTmVarToFcTerm :: RnTmVar -> FcTerm
rnTmVarToFcTerm = FcTmVar . rnTmVarToFcTmVar

-- * Type Unification
-- ------------------------------------------------------------------------------

-- | Type Unification. The first argument are the untouchables (rigid) variables.
unify :: MonadError CompileError m => [RnTyVar] -> EqCs -> m HsTySubst
unify _untchs [] = return mempty
unify  untchs eqs
  | Just ((subst1, eqs'), eqs'') <- go (one_step untchs) eqs
  = do subst2 <- unify untchs (substInEqCs subst1 (eqs' ++ eqs''))
       return (subst2 <> subst1)
  | otherwise = tcFail $ vcat [ text "Unification failed."
                                   , text "Residual constraints" <+> colon <+> ppr eqs
                                   , text "Untouchables"         <+> colon <+> ppr untchs ]
  where
    one_step :: [RnTyVar] -> EqCt -> Maybe (HsTySubst, EqCs)
    one_step _us (TyVar v1 :~: TyVar v2)
      | v1 == v2 = Just (mempty, [])
    one_step us (TyVar v :~: ty)
      | v `notElem` us, occursCheck v ty = Just (v |-> ty, [])
    one_step us (ty :~: TyVar v)
      | v `notElem` us, occursCheck v ty = Just (v |-> ty, [])
    one_step _us (_ :~: TyVar _) = Nothing
    one_step _us (TyVar _ :~: _) = Nothing
    one_step _us (TyCon tc1 :~: TyCon tc2)
      | tc1 == tc2 = Just (mempty, [])
      | otherwise  = Nothing
    one_step _us (TyApp ty1 ty2 :~: TyApp ty3 ty4)
      = Just (mempty, [ty1 :~: ty3, ty2 :~: ty4])
    one_step _us (TyCon {} :~: TyApp {}) = Nothing
    one_step _us (TyApp {} :~: TyCon {}) = Nothing

    go :: (a -> Maybe b) -> [a] -> Maybe (b, [a])
    go _p []     = Nothing
    go  p (x:xs) | Just y <- p x = Just (y, xs)
                 | otherwise     = second (x:) <$> go p xs

-- | Occurs Check
occursCheck :: RnTyVar -> RnMonoTy -> Bool
occursCheck _ (TyCon {})      = True
occursCheck a (TyApp ty1 ty2) = occursCheck a ty1 && occursCheck a ty2
occursCheck a (TyVar b)       = a /= b

-- * Overlap Checking
-- ------------------------------------------------------------------------------

overlapCheck :: MonadError CompileError m => FullTheory -> RnClsCt -> m ()
overlapCheck theory cls_ct@(ClsCt cls1 ty1)
  -- We only care about the instance theory
 =
  case catMaybes (fmap overlaps (theory_inst theory)) of
    msg:_ -> tcFail msg
    []    -> return ()
  where
    overlaps (_ :| scheme@(CtrScheme _ _ (ClsCt cls2 ty2)))
      | cls1 == cls2
      , Right {} <- unify [] [ty1 :~: ty2] =
        Just (text "overlapCheck:" $$ ppr cls_ct $$ ppr scheme)
      | otherwise = Nothing

-- * Constraint Entailment
-- ------------------------------------------------------------------------------

-- | Simplify the wanted type class constraints. Return the residual constraints
-- | and the dictionary substitution.
simplify :: [RnTyVar] -> ProgramTheory -> AnnClsCs -> TcM (AnnClsCs, FcTmSubst)
simplify _as _theory [] = return (mempty, mempty)
simplify as theory (ct:cs) =
  entail as theory ct >>= \case
    Nothing -> do
      (residual_cs, fc_tm_subst) <- simplify as theory cs
      return (ct:residual_cs, fc_tm_subst)
    Just (cs', fc_subst) -> do
      (residual_cs, fc_subst') <- simplify as theory $ cs' <> cs
      return (residual_cs, fc_subst' <> fc_subst)

-- | Entail a single type class constraint. Returns Nothing if nothing has been
-- | done. May produce additional class constraints.
entail :: [RnTyVar] -> ProgramTheory -> AnnClsCt -> TcM (Maybe (AnnClsCs, FcTmSubst))
entail _untch [] _cls_ct = return Nothing
entail as ((d' :| CtrScheme bs cls_cs (ClsCt cls2 ty2)):schemes) ct@(d :| ClsCt cls1 ty1)
  | cls1 == cls2
  , Right ty_subst <- unify as [ty1 :~: ty2] = do
    (d''s, ann_cls_cs) <- annotateCts $ substInClsCs ty_subst cls_cs
    fc_subbed_bs <- mapM elabMonoTy . substInTyVars ty_subst $ labelOf bs
    let ev_subst =
          d |->
           foldl
             FcTmApp
             (foldl FcTmTyApp (FcTmVar d') fc_subbed_bs)
             (FcTmVar <$> d''s)
    return $ Just (ann_cls_cs, ev_subst)
  | otherwise = entail as schemes ct

-- | Returns the (transitive) super class constaints of the type class constraint
-- | using the super class theory.
closure :: [RnTyVar] -> ProgramTheory -> AnnClsCt -> TcM (AnnClsCs, DictCtx)
closure untchs theory cls_ct = go theory cls_ct
  where
    go ((d_top :| CtrScheme alphas [ClsCt cls2 ty2] q):schemes) ct@(d :| ClsCt cls1 ty1)
      | cls1 == cls2
      , Right ty_subst <- unify untchs [ty1 :~: ty2] = do
        d' <- freshDictVar
        let sub_q = substInClsCt ty_subst q
        fc_subbed_alphas <-
          mapM elabMonoTy . substInTyVars ty_subst $ labelOf alphas
        let tm = FcTmApp
                   (foldl FcTmTyApp (FcTmVar d_top) fc_subbed_alphas)
                   (FcTmVar d)
        fc_sub_q <- elabClsCt sub_q
        let ctx = LetCtx d' fc_sub_q tm HoleCtx
        (cls_cs, ctx') <- go schemes ct
        (all_cs, ctx'') <- closureAll untchs theory (d' :| sub_q : cls_cs)
        return (d' :| sub_q : cls_cs <> all_cs, ctx <> ctx' <> ctx'')
      | otherwise = go schemes ct
    go [] _cls_ct = return (mempty, mempty)
    go _ _ =
      tcFail $
        text "closure" <+> colon <+>
          text "constraint scheme has too many implications"

closureAll :: [RnTyVar] -> ProgramTheory -> AnnClsCs -> TcM (AnnClsCs, DictCtx)
closureAll as theory cs =
  ((\(a, b) -> (mconcat a, mconcat b)) . unzip) <$> mapM (closure as theory) cs

-- | Elaborate a class declaration. Return
--   a) The data declaration for the class
--   b) The method implementation
--   c) The extended typing environment
elabClsDecl ::
     RnClsDecl
  -> TcM (FcFamDecl, FcDataDecl, FcValBind, [FcValBind], ProgramTheory, TcCtx)
elabClsDecl (ClsD rn_cs cls (a :| _) method method_ty) = do
  -- Generate a fresh type and data constructor for the class
  -- They should already be generated during renaming.
  tc <- lookupClsTyCon   cls
  dc <- lookupClsDataCon cls
  let fc_a = rnTyVarToFcTyVar a

  fc_tyfam <- lookupClsTyFam cls
  let fc_fam_decl = FcFamDecl fc_tyfam [fc_a] KStar

  -- Elaborate the superclass constraints (with full well-formedness checking also)
  fc_sc_tys <- extendCtxM a (kindOf a) (mapM wfElabClsCt rn_cs)

  -- Elaborate the method type (with full well-formedness checking also)
  (_kind, fc_method_ty) <- extendCtxM a (kindOf a) (wfElabPolyTy method_ty)

  -- Generate the datatype declaration
  let fc_ctx_ty = FcTyFam fc_tyfam [FcTyVar fc_a]
  let fc_data_decl =
        FcDataDecl
          tc
          [rnTyVarToFcTyVar a]
          [ ( dc
            , mempty
            , mempty
            , fc_ctx_ty : fc_sc_tys ++ [fc_method_ty])
          ]

  -- Generate the method implementation
  (fc_val_bind, hs_method_ty) <- elabMethodSig method a cls method_ty

  -- Construct the extended typing environment
  ty_ctx <- extendCtxM method hs_method_ty ask

  (sc_schemes, sc_decls) <- fmap unzip $ forM (zip [1..] rn_cs) $ \(i,sc_ct) -> do
    d  <- freshDictVar -- For the declaration
    da <- freshDictVar -- For the input dictionary

    let cls_head  = ClsCt cls (TyVar a) -- TC a
    fc_cls_head <- elabClsCt cls_head   -- T_TC a

    -- forall a. TC a => SC
    let scheme = CtrScheme [(a :| kindOf a)] [cls_head] sc_ct
    -- forall a. T_TC a -> upsilon_SC
    fc_scheme <- elabScheme scheme

    -- fresh vars for inverse dict, super class dicts, method
    xs <- replicateM (length rn_cs + 2) freshFcTmVar

    let fc_tm =
          FcTmTyAbs (rnTyVarToFcTyVar a) $
          FcTmAbs da fc_cls_head $
          FcTmCase
            (FcTmVar da)
            [ FcAlt
                (FcConPat dc [] [] (xs |: (fc_ctx_ty : fc_sc_tys ++ [fc_method_ty])))
                (FcTmVar (xs !! i))
            ]

    let proj = FcValBind d fc_scheme fc_tm

    return (d :| scheme, proj)

  return (fc_fam_decl, fc_data_decl, fc_val_bind, sc_decls, sc_schemes, ty_ctx)

-- | Elaborate a method signature to
--   a) a top-level binding
--   b) the actual source type (with the proper class qualification)
elabMethodSig :: RnTmVar -> RnTyVar -> RnClass-> RnPolyTy -> TcM (FcValBind, RnPolyTy)
elabMethodSig method a cls sigma = do
  -- Create fresh variables and substitute
  ([a'],a_subst) <- freshenRnTyVars [a]
  let (bs, cs, ty) = destructPolyTy sigma
  (bs',bs_subst) <- freshenRnTyVars (labelOf bs)
  let new_as = a':bs'
  let subst = a_subst <> bs_subst
  let cs' = substInClsCs subst (ClsCt cls (TyVar a):cs)
  let ty' = substInMonoTy subst ty

  -- Source and target method types
  let method_ty =
        constructPolyTy
          ( zipWithExact (:|) new_as (map kindOf new_as)
          , cs'
          , ty')
  (_kind, fc_method_ty) <- wfElabPolyTy method_ty

  dc <- lookupClsDataCon cls  -- pattern constructor
  super_cs <- lookupClsSuper cls
  -- n superclass variables + 2 for the method and inverse instances
  xs <- replicateM (length super_cs + 2) freshFcTmVar

  -- Annotate the constraints with fresh dictionary variables
  (ds, ann_cs) <- annotateCts $ cs'
  -- elaborate the annotated dictionary variables to System F term binders
  dbinds <- annCtsToTmBinds ann_cs

  let fc_bs = map rnTyVarToFcType bs'

  -- Elaborate the dictionary types
  let cs_subst = rnTyVarToFcTyVar a |-> rnTyVarToFcType a'
  fc_cs_tys <- (fmap (substFcTyInTy cs_subst)) <$> mapM elabClsCt super_cs

  -- Elaborate the type of the dictionary contained method
  fc_dict_method_ty <- elabPolyTy $ substInPolyTy a_subst sigma

  fc_tyfam <- lookupClsTyFam cls
  let fc_bi_ty = FcTyFam fc_tyfam []

  let fc_method_rhs =
        fcTmTyAbs (rnTyVarToFcTyVar <$> new_as) $
        fcTmAbs dbinds $
        FcTmCase
          (FcTmVar (head ds))
          [ FcAlt
              (FcConPat dc mempty mempty (xs |: (fc_bi_ty : fc_cs_tys ++ [fc_dict_method_ty])))
              (fcDictApp (fcTmTyApp (FcTmVar (last xs)) (fc_bs)) (tail ds))
          ]

  let fc_val_bind = FcValBind (rnTmVarToFcTmVar method) fc_method_ty fc_method_rhs

  return (fc_val_bind, method_ty)

-- | Elaborate a list of annotated dictionary variables to a list of System F term binders.
annCtsToTmBinds :: AnnClsCs -> TcM [(FcTmVar, FcType)]
annCtsToTmBinds = mapM (\(d :| ct) -> (,) d <$> elabClsCt ct)

-- * Data Declaration Elaboration
-- ------------------------------------------------------------------------------

-- | Elaborate a datatype declaration
elabDataDecl :: RnDataDecl -> TcM FcDataDecl
elabDataDecl (DataD tc as dcs) = do
  fc_tc <- hs_tc_fc_ty_con <$> lookupTcEnvM tc_env_tc_info tc  -- Elaborate the type constructor
  let fc_as = map (rnTyVarToFcTyVar . labelOf) as              -- Elaborate the universal type variables

  fc_dcs <- forM dcs $ \(dc, tys) -> do
    fc_dc <- hs_dc_fc_data_con <$> lookupTcEnvM tc_env_dc_info dc         -- Elaborate the data constructor
    (kinds, fc_tys) <- unzip <$> extendCtxKindAnnotatedTysM as (mapM wfElabMonoTy tys) -- Elaborate the argument types
    unless (all (==KStar) kinds) $
      tcFail (text "elabDataDecl" <+> colon <+> text "not all datacon args have kind star")
    return (fc_dc, mempty, mempty, fc_tys)
  return (FcDataDecl fc_tc fc_as fc_dcs)

-- | Extend the typing environment with some kind annotated type variables
extendCtxKindAnnotatedTysM :: [RnTyVarWithKind] -> TcM a -> TcM a
extendCtxKindAnnotatedTysM ann_as = extendCtxM as (map kindOf as)
  where
    as = map labelOf ann_as

-- * Class Instance Elaboration
-- ------------------------------------------------------------------------------

-- | Elaborate a class instance. Take the program theory also as input and return
--   a) The dictionary transformer implementation
--   b) The extended program theory
elabInsDecl :: FullTheory -> RnInsDecl -> TcM (FcAxiomDecl, [FcValBind], FullTheory)
elabInsDecl theory (InsD ins_cs cls typat method method_tm) = do
  let bs      = ftyvsOf typat
  let fc_bs   = map (rnTyVarToFcTyVar . labelOf) bs
  let head_ct = ClsCt cls (hsTyPatToMonoTy typat)

  -- Ensure the instance does not overlap
  overlapCheck theory head_ct

  -- Create the instance constraint scheme
  ins_d <- freshDictVar
  ins_scheme <- fmap (ins_d :|) $ freshenLclBndrs $ CtrScheme bs ins_cs head_ct

  ann_ins_cs <- snd <$> annotateCts ins_cs

  -- Elaborate the inverted type class instances
  (fc_axiom_decl, inv_proj_binds, fc_ctx, inv_schemes)
    <- elabBidirInst bs ann_ins_cs head_ct

  --  Generate fresh dictionary variables for the instance context
  (closure_cs, closure_ctx) <- closureAll
                                 (labelOf bs)
                                 (theory_super theory <> theory_bidir theory)
                                 ann_ins_cs
  let ann_ins_schemes = (fmap . fmap) (CtrScheme [] []) (closure_cs <> ann_ins_cs)

  -- The extended program theory
  let ext_theory = theory `ftExtendInst`  [ins_scheme]
                          `ftExtendBidir` (inv_schemes)

  --  The local program theory
  let local_theory = ext_theory `ftExtendLocal` ann_ins_schemes

  -- Create the dictionary transformer type
  dtrans_ty <- do
    fc_head_ty <- extendTcCtxTysM (labelOf bs) (wfElabClsCt head_ct)
    fc_ins_cs <- extendTcCtxTysM (labelOf bs) (wfElabClsCs ins_cs)
    return $ fcTyAbs fc_bs $ fcTyArr fc_ins_cs fc_head_ty

  -- Elaborate the method implementation
  fc_method_tm <- do
    expected_method_ty <- instMethodTy (hsTyPatToMonoTy typat) <$> lookupCtxM method
    elabTermWithSig (labelOf bs) local_theory method_tm expected_method_ty

  -- Entail the superclass constraints
  fc_super_tms <- do
    a <- lookupClsParam cls
    (ds, super_cs) <- substVar a (hsTyPatToMonoTy typat) <$>
                        lookupClsSuper cls >>= annotateCts

    (residual_cs, ev_subst) <- simplify
                                 (labelOf bs)
                                 (ftDropSuper local_theory) -- TODO apearantly these should not include the instance scheme
                                  super_cs

    unless (null residual_cs) $
      tcFail (text "Failed to resolve superclass constraints" <+>
                   colon <+>
                   ppr residual_cs $$ text "From" <+> colon <+> ppr local_theory)

    return $ substFcTmInTm ev_subst . FcTmVar <$> ds

  -- The full implementation of the dictionary transformer
  fc_dict_transformer <- do
    binds <- annCtsToTmBinds ann_ins_cs
    dc    <- lookupClsDataCon cls
    pat_ty <- elabMonoTy (hsTyPatToMonoTy typat)
    return $ fcTmTyAbs fc_bs $
      fcTmAbs binds $
        applyDictCtx closure_ctx $
          fcDataConApp dc pat_ty ( fc_ctx : fc_super_tms ++ [fc_method_tm])

  -- Resulting dictionary transformer
  let fc_val_bind = FcValBind ins_d dtrans_ty fc_dict_transformer

  return (fc_axiom_decl, fc_val_bind : inv_proj_binds, ext_theory)

-- | Instantiate a method type for a particular instance
instMethodTy :: RnMonoTy -> RnPolyTy -> RnPolyTy
instMethodTy typat poly_ty = constructPolyTy (new_as, new_cs, new_ty)
  where
    ((a :| _kind):as,_c:cs,ty) = destructPolyTy poly_ty
    subst      = (a |-> typat)
    new_as     = as
    new_cs     = substInClsCs  subst cs
    new_ty     = substInMonoTy subst ty

-- | Elaborates the inverted type class instances.
-- Returns the inverted context Fc axiom, the inverted dictionary projections,
-- the dictionary context and the inverted constraint schemes.
elabBidirInst :: [RnTyVarWithKind] -> AnnClsCs -> RnClsCt
              -> TcM (FcAxiomDecl, [FcValBind], FcTerm, ProgramTheory)
elabBidirInst bs ann_ins_cs head_ct@(ClsCt cls param_ty) = do
  let fc_bs = rnTyVarToFcTyVar . labelOf <$> bs
  fc_head_ct <- elabClsCt head_ct
  fc_param_ty <- elabMonoTy param_ty
  inv_ds <- genFreshDictVars $ length ann_ins_cs
  inv_d_tys <- mapM elabClsCt $ dropLabel ann_ins_cs
  let ins_cs = dropLabel ann_ins_cs

  g <- freshFcAxVar
  f <- lookupClsTyFam cls
  (fc_tuple_tc, fc_tuple_dc) <- lookupFcTuple $ length ann_ins_cs
  let fc_axiom_decl =
        FcAxiomDecl g fc_bs f [fc_param_ty] (fcTyApp (FcTyCon fc_tuple_tc) inv_d_tys)

  a <- lookupClsParam cls
  super_cs <- substVar a param_ty <$> lookupClsSuper cls
  ann_super_cs <- snd <$> annotateCts super_cs
  fc_super_binds <- fmap (uncurry (:|)) <$> annCtsToTmBinds ann_super_cs

  dc <- lookupClsDataCon cls
  fc_method_ty <- elabPolyTy =<< instMethodTy param_ty <$>
                    (lookupCtxM =<< lookupClsMethod cls)
  fc_method <- freshFcTmVar
  (inv_schemes, inv_proj_binds) <- unzip <$> (forM (zipExact inv_ds ins_cs) $ \(di,ins_ct) -> do
    let scheme' = CtrScheme bs [head_ct] ins_ct
    scheme <- freshenLclBndrs scheme'
    inv_proj_ty <- elabScheme scheme'
    d <- freshDictVar
    ctx <- freshFcTmVar
    let inv_proj =
          fcTmTyAbs fc_bs $
          FcTmAbs d fc_head_ct $
          FcTmCase (FcTmVar d) $
          [ FcAlt
              (FcConPat
                 dc
                 mempty
                 mempty
                 (ctx :| FcTyFam f [fc_param_ty] :
                  fc_super_binds ++ [fc_method :| fc_method_ty]))
              (FcTmCase
                 (FcTmCast (FcTmVar ctx) (FcCoAx g (FcTyVar <$> fc_bs)))
                 [ FcAlt
                     (FcConPat fc_tuple_dc mempty mempty (inv_ds |: inv_d_tys))
                     (FcTmVar di)
                 ])
          ]
    di' <- freshDictVar
    let inv_proj_bind = FcValBind di' inv_proj_ty inv_proj
    return (di' :| scheme,inv_proj_bind))

  let fc_ctx =
        FcTmCast
          (fcTmApp
             (fcTmTyApp (FcTmDataCon fc_tuple_dc) inv_d_tys)
             (FcTmVar <$> (labelOf ann_ins_cs)))
          (FcCoSym (FcCoAx g (FcTyVar <$> fc_bs)))

  return (fc_axiom_decl, inv_proj_binds, fc_ctx, inv_schemes)

-- | Elaborate a term with an explicit type signature (method implementation).
-- This involves both inference and type subsumption.
elabTermWithSig :: [RnTyVar] -> FullTheory -> RnTerm -> RnPolyTy -> TcM FcTerm
elabTermWithSig untch theory tm poly_ty = do
  let (as, cs, ty) = destructPolyTy poly_ty
  let fc_as = map rnTyVarToFcTyVar (labelOf as)
  let untouchables = nub (untch ++ map labelOf as)

  -- Infer the type of the expression and the wanted constraints
  ((mono_ty, fc_tm), wanted_eqs, wanted_ccs) <- runGenM $ elabTerm tm


  -- Generate fresh dictionary variables for the given constraints
  given_ccs <- snd <$> annotateCts cs
  dbinds <- annCtsToTmBinds given_ccs
  (super_cs, closure_ctx) <-
    closureAll
      untouchables
      (theory_super theory <> theory_bidir theory)
      given_ccs
  let given_schemes = (fmap . fmap) (CtrScheme [] []) (super_cs <> given_ccs)

  -- Resolve all the wanted constraints
  ty_subst <- unify untouchables $ wanted_eqs ++ [mono_ty :~: ty]
  let local_theory = ftDropSuper theory <> given_schemes
  let wanted = substInAnnClsCs ty_subst wanted_ccs

   -- rightEntailsRec untouchables local_theory wanted
  (residual_cs, ev_subst) <- simplify untouchables local_theory wanted

  -- Ensure that the constraints are completely resolved
  unless (null residual_cs) $
    tcFail
      (text "Failed to resolve constraints" <+>
       colon <+> ppr residual_cs $$ text "From" <+> colon <+> ppr theory
       $$ text "Wanted" <+> colon <+> ppr wanted)
  fc_subst <- elabHsTySubst ty_subst

  -- Generate the resulting System F term
  return $
    fcTmTyAbs fc_as $
    fcTmAbs dbinds $
    applyDictCtx closure_ctx $
      substFcTmInTm ev_subst $
        substFcTyInTm fc_subst fc_tm

-- | Convert a source type substitution to a System F type substitution
elabHsTySubst :: HsTySubst -> TcM FcTySubst
elabHsTySubst = mapSubM (return . rnTyVarToFcTyVar) elabMonoTy

-- * Type Inference With Constraint Simplification
-- ------------------------------------------------------------------------------

elabTermSimpl :: ProgramTheory -> RnTerm -> TcM (RnPolyTy, FcTerm)
elabTermSimpl theory tm = do
  -- Infer the type of the expression and the wanted constraints
  ((mono_ty, fc_tm), wanted_eqs, wanted_ccs) <- runGenM $ elabTerm tm

  -- Simplify as much as you can
  ty_subst <- unify mempty $ wanted_eqs -- Solve the needed equalities first

  let refined_wanted_ccs = substInAnnClsCs      ty_subst wanted_ccs             -- refine the wanted class constraints
  let refined_mono_ty    = substInMonoTy        ty_subst mono_ty                -- refine the monotype
  -- refine the term
  refined_fc_tm <- flip substFcTyInTm fc_tm <$> elabHsTySubst ty_subst

  let untouchables = nub (ftyvsOf refined_wanted_ccs ++ ftyvsOf refined_mono_ty)

  (residual_cs, ev_subst) <- simplify untouchables theory refined_wanted_ccs

  -- Generalize the type
  let new_mono_ty = refined_mono_ty
  let new_cs      = map dropLabel (residual_cs) -- refined_wanted_ccs) -- residual_cs)
  let new_as      = untouchables
  let gen_ty      = constructPolyTy (map (\a -> a :| kindOf a) new_as, new_cs, new_mono_ty)

  -- Elaborate the term
  let fc_as = map rnTyVarToFcTyVar new_as
  dbinds   <- annCtsToTmBinds residual_cs -- refined_wanted_ccs --residual_cs
  let full_fc_tm = fcTmTyAbs fc_as $
                     fcTmAbs dbinds $
                       substFcTmInTm ev_subst $
                         refined_fc_tm

  return (gen_ty, full_fc_tm)

-- * Value Binding Elaboration
-- ------------------------------------------------------------------------------

-- | Elaborate a top-level value binding
elabValBind :: FullTheory -> RnValBind -> TcM (FcValBind, TcCtx)
elabValBind theory (ValBind a m_ty tm) = do
  (ty,fc_tm) <- case m_ty of
    Nothing -> elabTermSimpl (ftDropSuper theory) tm
    Just ty -> do
      fc_tm <- elabTermWithSig [] theory tm ty
      return (ty,fc_tm)
  ctx <- ask
  fc_ty <- elabPolyTy ty
  let fc_val_bind = FcValBind (rnTmVarToFcTmVar a) fc_ty fc_tm
  return (fc_val_bind, extendCtx ctx a ty)

-- * Primitive Elaboration
-- ------------------------------------------------------------------------------

-- | Elaborate various primitives (just tuples for now)
elabPrimitives :: TcM [FcDataDecl]
elabPrimitives = do
  AssocList tuples <- tc_env_tuples <$> get
  forM (snocListToList tuples) $ \(arity, (tc, dc)) -> do
    as <- replicateM arity (freshFcTyVar KStar)
    return $ FcDataDecl tc as [(dc, mempty, mempty, FcTyVar <$> as)]

-- * Program Elaboration
-- ------------------------------------------------------------------------------

-- | Elaborate a program
elabProgram :: FullTheory -> RnProgram
            -> TcM ( FcProgram       {- Elaborated program       -}
                   , RnPolyTy        {- Term type (MonoTy?)      -}
                   , FullTheory )    {- Final program theory     -}
-- Elaborate the program expression
elabProgram theory (PgmExp tm) = do
  (ty, fc_tm) <- elabTermSimpl (ftDropSuper theory) tm
  fc_prim_decls <- elabPrimitives
  let fc_program = foldr FcPgmDataDecl (FcPgmTerm fc_tm) fc_prim_decls
  return (fc_program, ty, theory)

-- Elaborate a class declaration
elabProgram theory (PgmCls cls_decl pgm) = do
  (fc_fam_decl, fc_data_decl, fc_val_bind, fc_sc_proj, ext_theory, ext_ty_env) <-
    elabClsDecl cls_decl
  (fc_pgm, ty, final_theory) <-
    setTcCtxTmM ext_ty_env (elabProgram (theory `ftExtendSuper` ext_theory) pgm)
  let fc_program =
        FcPgmFamDecl fc_fam_decl $
        FcPgmDataDecl
          fc_data_decl
          (FcPgmValDecl
             fc_val_bind
             (foldl (flip FcPgmValDecl) fc_pgm fc_sc_proj))
  return (fc_program, ty, final_theory)

-- | Elaborate a class instance
elabProgram theory (PgmInst ins_decl pgm) = do
  (fc_axiom_decl, fc_val_binds, ext_theory) <- elabInsDecl theory ins_decl
  (fc_pgm, ty, final_theory) <- elabProgram ext_theory pgm
  let fc_program =
        FcPgmAxiomDecl fc_axiom_decl $ foldr FcPgmValDecl fc_pgm fc_val_binds
  return (fc_program, ty, final_theory)

-- Elaborate a datatype declaration
elabProgram theory (PgmData data_decl pgm) = do
  fc_data_decl <- elabDataDecl data_decl
  (fc_pgm, ty, final_theory) <- elabProgram theory pgm
  let fc_program = FcPgmDataDecl fc_data_decl fc_pgm
  return (fc_program, ty, final_theory)

-- Elaborate a top-level value binding
elabProgram theory (PgmVal val_bind pgm) = do
  (fc_val_bind, ext_ctx) <- elabValBind theory val_bind
  (fc_pgm, ty, final_theory) <- setCtxM ext_ctx $ elabProgram theory pgm
  let fc_program = FcPgmValDecl fc_val_bind fc_pgm
  return (fc_program, ty, final_theory)

-- * Invoke the complete type checker
-- ------------------------------------------------------------------------------

hsElaborate ::
     RnEnv
  -> UniqueSupply
  -> RnProgram
  -> Either CompileError ( (((FcProgram, RnPolyTy, FullTheory)), UniqueSupply)
                         , TcEnv)
hsElaborate rn_gbl_env us pgm = runExcept
                              $ flip runStateT  tc_init_gbl_env -- Empty when you start
                              $ flip runReaderT tc_init_ctx
                              $ flip runUniqueSupplyT us
                              $ markErrorPhase HsTypeChecker
                              $ do buildInitTcEnv pgm rn_gbl_env -- Create the actual global environment
                                   elabProgram tc_init_theory pgm
  where
    tc_init_theory  = FT mempty mempty mempty mempty
    tc_init_ctx     = mempty
    tc_init_gbl_env = TcEnv mempty mempty mempty mempty

tcFail :: MonadError CompileError m => Doc -> m a
tcFail = throwError . CompileError HsTypeChecker
