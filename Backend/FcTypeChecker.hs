{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE LambdaCase           #-}

module Backend.FcTypeChecker (fcTypeCheck) where

import Backend.FcTypes

import Utils.Substitution
import Utils.Var
import Utils.Kind
import Utils.Unique
import Utils.AssocList
import Utils.Ctx
import Utils.PrettyPrint hiding ((<>))
import Utils.Errors
import Utils.Utils
import Utils.Annotated

import Control.Monad.Writer
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except

-- * Type checking monad
-- ----------------------------------------------------------------------------
type FcM = UniqueSupplyT (ReaderT FcTcCtx (StateT FcGblEnv (Except CompileError)))

data FcGblEnv = FcGblEnv { fc_env_tc_info :: AssocList FcTyCon   FcTyConInfo
                         , fc_env_dc_info :: AssocList FcDataCon FcDataConInfo
                         , fc_env_tf_info :: AssocList FcTyFam   FcFamInfo
                         , fc_env_ax_info :: AssocList FcAxVar   FcAxiomInfo
                         }

instance PrettyPrint FcGblEnv where
  ppr (FcGblEnv tc_infos dc_infos tf_infos ax_infos)
    = braces $ vcat $ punctuate comma
    [ text "fc_env_tc_info" <+> colon <+> ppr tc_infos
    , text "fc_env_dc_info" <+> colon <+> ppr dc_infos
    , text "fc_env_tf_info" <+> colon <+> ppr tf_infos
    , text "fc_env_ax_info" <+> colon <+> ppr ax_infos ]
  needsParens _ = False

-- * Lookup things in the global environment
-- ----------------------------------------------------------------------------

-- | Lookup something in the global environment
lookupFcGblEnvM :: (Eq a, PrettyPrint a, MonadError CompileError m, MonadState s m) => (s -> AssocList a b) -> a -> m b
lookupFcGblEnvM f x = gets f >>= \l -> case lookupInAssocList x l of
  Just y  -> return y
  Nothing -> fcFail (text "lookupFcGblEnvM" <+> colon <+> ppr x <+> text "is unbound")

-- | Lookup the info of a type constructor
lookupTyConInfoM :: FcTyCon -> FcM FcTyConInfo
lookupTyConInfoM = lookupFcGblEnvM fc_env_tc_info

-- | Lookup the kind of a type constructor
lookupTyConKindM :: FcTyCon -> FcM Kind
lookupTyConKindM tc = foldr KArr KStar . map kindOf . fc_tc_type_args <$> lookupTyConInfoM tc

-- | Lookup the info of a data constructor
lookupDataConInfoM :: FcDataCon -> FcM FcDataConInfo
lookupDataConInfoM = lookupFcGblEnvM fc_env_dc_info

-- | Lookup the type of a data constructor
lookupDataConTyM :: FcDataCon -> FcM ([FcTyVar], [FcTyVar], [FcProp], [FcType], FcTyCon)
lookupDataConTyM dc = lookupDataConInfoM dc >>= \info ->
  return (fc_dc_univ info, fc_dc_exis info, fc_dc_prop info, fc_dc_arg_tys info, fc_dc_parent info)

-- | Lookup the info of a type family
lookupFamInfoM :: FcTyFam -> FcM FcFamInfo
lookupFamInfoM = lookupFcGblEnvM fc_env_tf_info

-- | Lookup the info an equality axiom
lookupAxiomInfoM :: FcAxVar -> FcM FcAxiomInfo
lookupAxiomInfoM = lookupFcGblEnvM fc_env_ax_info

-- | Add type family info to the global environment
addFamInfoM :: FcFamInfo -> FcM ()
addFamInfoM info =
  modify
    (\env ->
       env
       { fc_env_tf_info =
           extendAssocList (fc_fam_var info) info (fc_env_tf_info env)
       })

-- | Add equality axiom info to the global environment
addAxiomInfoM :: FcAxiomInfo -> FcM ()
addAxiomInfoM info =
  modify
    (\env ->
       env
       { fc_env_ax_info =
           extendAssocList (fc_ax_var info) info (fc_env_ax_info env)
       })

-- | Add data constructor info to the global environment
addDataConInfoM :: FcDataConInfo -> FcM ()
addDataConInfoM info =
  modify
    (\env ->
       env
       { fc_env_dc_info =
           extendAssocList (fc_dc_data_con info) info (fc_env_dc_info env)
       })

-- | Add data constructor info to the global environment
addTyConInfoM :: FcTyConInfo -> FcM ()
addTyConInfoM info =
  modify
    (\env ->
       env
       { fc_env_tc_info =
           extendAssocList (fc_tc_ty_con info) info (fc_env_tc_info env)
       })

-- | Check if something is not currently bound in the global environment
notInFcGblEnvM :: (Eq a, PrettyPrint a, MonadError CompileError m, MonadState s m) => (s -> AssocList a b) -> a -> m ()
notInFcGblEnvM f x = gets f >>= \l -> case lookupInAssocList x l of
  Just _  -> fcFail (text "notInFcGblEnvM" <+> colon <+> ppr x <+> text "is already bound")
  Nothing -> return ()

-- * Building the global environment
-- ----------------------------------------------------------------------------

-- | Build the global environment with info from top-level declarations
buildInitFcEnv :: FcProgram -> FcM ()
buildInitFcEnv (FcPgmDataDecl (FcDataDecl tc as dcs) pgm) = do
  notInFcGblEnvM fc_env_tc_info tc
  addTyConInfoM (FcTCInfo tc as)
  forM_ dcs $ \(dc,bs,props,tys) -> do
    notInFcGblEnvM fc_env_dc_info dc
    addDataConInfoM (FcDCInfo dc as bs props tc tys)
  buildInitFcEnv pgm
buildInitFcEnv (FcPgmFamDecl (FcFamDecl f as k) pgm) = do
  notInFcGblEnvM fc_env_tf_info f
  addFamInfoM (FcFamInfo f as k)
  buildInitFcEnv pgm
buildInitFcEnv (FcPgmAxiomDecl (FcAxiomDecl g as fam us v) pgm) = do
  notInFcGblEnvM fc_env_ax_info g
  addAxiomInfoM (FcAxiomInfo g as fam us v)
  buildInitFcEnv pgm
buildInitFcEnv (FcPgmValDecl _decl pgm) = buildInitFcEnv pgm
buildInitFcEnv (FcPgmTerm _term) = return ()

-- * Type checking
-- ----------------------------------------------------------------------------

-- | Type check a data declaration
tcFcDataDecl :: FcDataDecl -> FcM ()
tcFcDataDecl (FcDataDecl _tc as dcs) = do
  forM_ as notInCtxM
  forM_ dcs $ \(_dc, bs, psis, tys) -> do
    let ty_vars = as <> bs
    kinds <- extendCtxM ty_vars (kindOf <$> ty_vars)
               (mapM_ tcProp psis >> mapM tcType tys)
    unless (all (==KStar) (kinds) ) $
      fcFail $ text "tcFcDataDecl: Kind mismatch (FcDataDecl)"

-- | Type check a top-level value binding
tcFcValBind :: FcValBind -> FcM FcTcCtx
tcFcValBind (FcValBind x ty tm) = do
  notInCtxM x  -- Ensure is not already bound
  kind <- tcType ty
  unless (kind == KStar) $
    fcFail $ text "tcFcValBind: Kind mismatch (FcValBind)"
  ty' <- extendCtxM x ty (tcTerm tm)
  unless (ty `eqFcTypes` ty') $ fcFail (text "Global let type doesnt match:"
                                $$ parens (text "given:" <+> ppr ty)
                                $$ parens (text "inferred:" <+> ppr ty'))
  extendCtxM x ty ask -- Return the extended environment

-- | Type check a equality axiom declaration
tcFcAxiomDecl :: FcAxiomDecl -> FcM ()
tcFcAxiomDecl (FcAxiomDecl _g as fam us v) = do
  mapM_ notInCtxM as
  FcFamInfo _ as' kind <- lookupFamInfoM fam
  unless (length us == length as') $
    fcFail $
    text "tcFcAxiomDecl" <+> colon <+> text "quantified variables length mismatch"
  (k:ks) <- extendCtxM as (kindOf <$> as) $ mapM tcType (v : us)
  unless (kind == k) $
    fcFail $
    text "tcFcAxiomDecl" <+> colon <+> text "family return kind mismatch"
  unless (ks == (kindOf <$> as')) $
    fcFail $
    text "tcFcAxiomDecl" <+> colon <+> text "parameter kind mismatch"

-- | Type check a type family declaration
tcFcFamDecl :: FcFamDecl -> FcM ()
tcFcFamDecl (FcFamDecl _f as _k) = mapM_ notInCtxM as

-- | Type check a program
tcFcProgram :: FcProgram -> FcM FcType
-- Type check a datatype declaration
tcFcProgram (FcPgmDataDecl datadecl pgm) = do
  tcFcDataDecl datadecl
  tcFcProgram pgm
-- Type check a top-level value binding
tcFcProgram (FcPgmValDecl valbind pgm) = do
  fc_ctx <- tcFcValBind valbind
  setCtxM fc_ctx $ tcFcProgram pgm
-- Type check a equality axiom declaration
tcFcProgram (FcPgmAxiomDecl axdecl pgm) = do
  tcFcAxiomDecl axdecl
  tcFcProgram pgm
-- Type check a type family declaration
tcFcProgram (FcPgmFamDecl famdecl pgm) = do
  tcFcFamDecl famdecl
  tcFcProgram pgm
-- Type check the top-level program expression
tcFcProgram (FcPgmTerm tm) = tcTerm tm

-- | Type check a System Fc term
tcTerm :: FcTerm -> FcM FcType
tcTerm (FcTmAbs x ty1 tm) = do
  kind <- tcType ty1 -- Should have kind star
  unless (kind == KStar) $
    fcFail $ text "tcTerm: Kind mismatch (FcTmAbs)"
  ty2  <- extendCtxM x ty1 (tcTerm tm)
  return (mkFcArrowTy ty1 ty2)
tcTerm (FcTmVar x) = lookupCtxM x
tcTerm (FcTmApp tm1 tm2)  = do
  ty1 <- tcTerm tm1
  ty2 <- tcTerm tm2
  case isFcArrowTy ty1 of
    Just (ty1a, ty1b) -> alphaEqFcTypes ty1a ty2 >>= \case
      True  -> return ty1b
      False -> fcFail (text "tcTerm" <+> text "FcTmApp" $$ pprPar ty1 $$ pprPar ty2)
    Nothing           -> fcFail (text "Wrong function FcType application"
                                      $$ parens (text "ty1=" <+> ppr ty1)
                                      $$ parens (text "ty2=" <+> ppr ty2)
                                      $$ parens (text "tm1=" <+> ppr tm1)
                                      $$ parens (text "tm2=" <+> ppr tm2))

tcTerm (FcTmTyAbs a tm) = do
  notInCtxM a -- Ensure not already bound
  ty <- extendCtxM a (kindOf a) (tcTerm tm)
  return (FcTyAbs a ty)
tcTerm (FcTmTyApp tm ty) = do
  kind <- tcType ty
  tcTerm tm >>= \case
    FcTyAbs a tm_ty
      | kindOf a == kind -> return $ substVar a ty tm_ty
    _other               -> fcFail $ text "Malformed type application"

tcTerm (FcTmDataCon dc) = mkDataConTy <$> lookupDataConTyM dc
  where
    mkDataConTy (as, bs, psis, arg_tys, tc) =
      fcTyAbs as $
      fcTyAbs bs $
      fcTyQual psis $
      fcTyArr arg_tys $
        fcTyConApp tc (map FcTyVar as)
tcTerm (FcTmLet x ty tm1 tm2) = do
  notInCtxM x -- Ensure not already bound
  kind <- tcType ty
  unless (kind == KStar) $
    fcFail $ text "tcTerm: Kind mismatch (FcTmLet)"
  ty1  <- extendCtxM x ty (tcTerm tm1)
  unless (ty `eqFcTypes` ty1) $ fcFail $ text "Let type doesnt match"
  extendCtxM x ty (tcTerm tm2)
tcTerm (FcTmCase scr alts) = do
  scr_ty <- tcTerm scr
  tcAlts scr_ty alts
tcTerm (FcTmPropAbs c psi tm) = do
  notInCtxM c
  tcProp psi
  FcTyQual psi <$> extendCtxM c psi (tcTerm tm)
tcTerm (FcTmCoApp tm co) = tcTerm tm >>= \case
  (FcTyQual psi2 ty) -> do
    psi1 <- tcCoercion co
    unless (eqFcProp psi1 psi2) $
      fcFail $ text "tcTerm: coercion does not match (FcTmCoApp)"
            $$ text "tm" <+> colon <+> ppr tm
            $$ text "co" <+> colon <+> ppr co
    return ty
  _ -> fcFail $ text "tcTerm: term should have a qualified type (FcTmCoApp)"
             $$ text "tm" <+> colon <+> ppr tm
             $$ text "co" <+> colon <+> ppr co
tcTerm (FcTmCast tm co) = do
  ty <- tcTerm tm
  FcProp ty1 ty2 <- tcCoercion co
  unless (eqFcTypes ty ty1) $
    fcFail $ text "tcTerm: term and coercion type don't match (FcTmCast)"
          $$ text "tm" <+> colon <+> ppr tm
          $$ text "co" <+> colon <+> ppr co
  return ty2

-- | Kind check a type
tcType :: FcType -> FcM Kind
tcType (FcTyVar a) = lookupCtxM a
tcType (FcTyAbs a ty) = do
  notInCtxM a            -- Ensure not already bound
  k <- extendCtxM a (kindOf a) (tcType ty)
  case k of
    KStar  -> return KStar
    _other -> fcFail $ text "tcType: Kind mismatch (FcTyAbs)"
tcType (FcTyApp ty1 ty2) = do
  k1 <- tcType ty1
  k2 <- tcType ty2
  case k1 of
    KArr k1a k1b | k1a == k2 -> return k1b
    _otherwise               -> fcFail $ text "tcType: Kind mismatch (FcTyApp)"
tcType (FcTyCon tc) = lookupTyConKindM tc
tcType (FcTyQual psi ty) = tcProp psi >> tcType ty
tcType (FcTyFam f tys) = do
  FcFamInfo _f as k <- lookupFamInfoM f
  unless (length as == length tys) $
    fcFail $ text "tcType: mismatch in amount of parameters (FcTyFam)"
  ks <- mapM tcType tys
  unless ((kindOf <$> as) == ks) $
    fcFail $ text "tcType : Kind mismatch (FcTyFam)"
  return k

-- | Type check a list of case alternatives
tcAlts :: FcType -> [FcAlt] -> FcM FcType
tcAlts scr_ty alts
  | null alts = fcFail $ text "Case alternatives are empty"
  | otherwise = do
      rhs_tys <- mapM (tcAlt scr_ty) alts
      ensureIdenticalTypes rhs_tys
      let (ty:_) = rhs_tys
      return ty

-- | Type check a single case alternative
tcAlt :: FcType -> FcAlt -> FcM FcType
tcAlt scr_ty alt@(FcAlt (FcConPat dc bs cs xs) rhs) = case tyConAppMaybe scr_ty of
  Just (tc, tys) -> do -- T tys
    mapM_ notInCtxM bs
    mapM_ notInCtxM (labelOf cs)
    mapM_ notInCtxM (labelOf xs)
    (as, bs', psis, arg_tys, dc_tc) <- lookupDataConTyM dc
    unless (dc_tc == tc) $
      patError "The type of the scrutinee does not match that of the pattern"
    let as_subst = mconcat (zipWithExact (|->) as tys)
    let bs_subst = mconcat (zipWithExact (|->) bs' (FcTyVar <$> bs))
    let ty_subst = as_subst <> bs_subst
    let real_arg_tys = substFcTyInTy ty_subst <$> arg_tys
    let real_psis = substFcTyInProp ty_subst <$> psis
    unlessM
      (and <$>
       (sequence $ zipWithExact alphaEqFcTypes real_arg_tys (dropLabel xs))) $
      patError "The types of the pattern arguments do not match"
    unless (and (zipWithExact eqFcProp real_psis (dropLabel cs))) $
      patError "The types of the coercions do not match"
    extendCtxM (labelOf xs) real_arg_tys $
      extendCtxM (labelOf cs) real_psis $ tcTerm rhs
  Nothing ->
    fcFail (text "destructScrTy" <+> colon <+> text "Not a tycon application")
  where
    patError str = fcFail $ text "tcAlt" <+> colon <+> text str
                          $$ ppr alt

-- | Type check a coercion
tcCoercion :: FcCoercion -> FcM FcProp
tcCoercion (FcCoVar c) = lookupCtxM c
tcCoercion (FcCoAx g tys) = do
  axiom <- lookupAxiomInfoM g
  let universal_vars = fc_ax_uv axiom
  unless (length universal_vars == length tys) $
    fcFail $ text "tcCoercion: incorrect amount of types applied to axiom variable (FcCoAx)"
          $$ text "g"   <+> colon <+> ppr g
          $$ text "tys" <+> colon <+> ppr tys
  mapM_ tcType tys
  return $
    substFcTyInProp (buildSubst (zip universal_vars tys)) (axiomToProp axiom)
tcCoercion (FcCoRefl ty) = do
  _ <- tcType ty
  return $ FcProp ty ty
tcCoercion (FcCoSym co) = do
  FcProp ty1 ty2 <- tcCoercion co
  return $ FcProp ty2 ty1
tcCoercion (FcCoTrans co1 co2) = do
  FcProp ty1  ty2 <- tcCoercion co1
  FcProp ty2' ty3 <- tcCoercion co2
  unless (eqFcTypes ty2 ty2') $
    fcFail $ text "tcCoercion: coercion types don't match (FcCoTrans)"
          $$ text "co1" <+> colon <+> ppr co1
          $$ text "co2" <+> colon <+> ppr co2
  return $ FcProp ty1 ty3
tcCoercion (FcCoApp co1 co2) = do
  FcProp ty1 ty2 <- tcCoercion co1
  FcProp ty3 ty4 <- tcCoercion co2
  let ty1ty3 = FcTyApp ty1 ty3
  let ty2ty4 = FcTyApp ty2 ty4
  k1 <- tcType ty1ty3
  k2 <- tcType ty2ty4
  unless (k1 == k2) $
    fcFail (text "FcCoApp" <+> colon <+> text "kind mismatch")
  return $ FcProp ty1ty3 ty2ty4
tcCoercion (FcCoLeft co) = tcCoercion co >>= \case
    FcProp (FcTyApp ty1 _ty2) (FcTyApp ty3 _ty4) ->
      return $ FcProp ty1 ty3
    _ ->
      fcFail $ text "tcCoercion: expected two type applications (FcCoLeft)"
            $$ text "co" <+> colon <+> ppr co
tcCoercion (FcCoRight co) = tcCoercion co >>= \case
    FcProp (FcTyApp _ty1 ty2) (FcTyApp _ty3 ty4) ->
      return $ FcProp ty2 ty4
    _ ->
      fcFail $ text "tcCoercion: expected two type applications (FcCoRight)"
            $$ text "co" <+> colon <+> ppr co
tcCoercion (FcCoFam f crcs) = do
  info <- lookupFamInfoM f
  unless (length crcs == length (fc_fam_univ info)) $
    fcFail $ text "tcCoercion: incorrent amount of coercions applied to type family (FcCoFam)"
          $$ text "f"    <+> colon <+> ppr f
          $$ text "crcs" <+> colon <+> ppr crcs
  (tys1, tys2) <- unzip . (fmap propToTuple) <$> mapM tcCoercion crcs
  ks1 <- mapM tcType tys1
  ks2 <- mapM tcType tys2
  unless (ks1 == ks2) $
    fcFail $ text "FcCoFam" <+> colon <+> text "kind mismatch"
  return $ FcProp (FcTyFam f tys1) (FcTyFam f tys2)
  where
    propToTuple (FcProp ty1 ty2) = (ty1, ty2)
tcCoercion (FcCoAbs a co) = do
  notInCtxM a
  (ty1, ty2) <- extendCtxM a (kindOf a) $ do
    FcProp ty1 ty2 <- tcCoercion co
    k1 <- tcType ty1
    k2 <- tcType ty2
    unless (k1 == k2) $ fcFail $
      text "FcCoAbs" <+> colon <+> text "kind mismatch"
    return (ty1, ty2)
  return $ FcProp (FcTyAbs a ty1) (FcTyAbs a ty2)
tcCoercion (FcCoInst co1 co2) = tcCoercion co1 >>= \case
  FcProp (FcTyAbs a ty1) (FcTyAbs b ty2) -> do
    unless (a == b) $
      fcFail $ text "tcCoerion: type abstractions have different type variables (FcCoInst)"
            $$ text "co1" <+> colon <+> ppr co1
            $$ text "co2" <+> colon <+> ppr co2
    k1 <- tcType ty1
    k2 <- tcType ty2 -- can't hurt
    unless (k1 == k2) $ fcFail $
      text "FcCoInst" <+> colon <+> text "kind mismatch"
    FcProp ty3 ty4 <- tcCoercion co2
    return $ FcProp (substVar a ty3 ty1) (substVar b ty4 ty2)
  _ -> fcFail $ text "tcCoercion: expected type abstrations (FcCoInst)"
             $$ text "co1" <+> colon <+> ppr co1
             $$ text "co2" <+> colon <+> ppr co2
tcCoercion (FcCoQual psi co) = do
  FcProp ty1 ty2 <- tcCoercion co
  tcProp psi
  return $ FcProp (FcTyQual psi ty1) (FcTyQual psi ty2)
tcCoercion (FcCoQInst co1 co2) = tcCoercion co1 >>= \case
  FcProp (FcTyQual psi1 ty1) (FcTyQual psi2 ty2) -> do
    prop <- tcCoercion co2
    unless (eqFcProp prop psi1 && eqFcProp prop psi2) $
      fcFail $ text "tcCoercion: coercions aren't equal (FcCoQInst)"
            $$ text "co1" <+> colon <+> ppr co1
            $$ text "co2" <+> colon <+> ppr co2
    return $ FcProp ty1 ty2
  _ -> fcFail $ text "tcCoercion: expected qualified types (FcCoQInst)"
             $$ text "co1" <+> colon <+> ppr co1
             $$ text "co2" <+> colon <+> ppr co2

-- | Type check propositions
tcProp :: FcProp -> FcM ()
tcProp (FcProp ty1 ty2) = do
  unlessM ((==) <$> tcType ty1 <*> tcType ty2) $
    fcFail $ text "FcProp" <+> colon <+> text "kind mismatch"

-- | Ensure that all types are syntactically the same
ensureIdenticalTypes :: [FcType] -> FcM ()
ensureIdenticalTypes types = unless (go types) $ fcFail $ text "Type mismatch in case rhs"
  where
    go :: [FcType] -> Bool
    go []       = True
    go (ty:tys) = all (eqFcTypes ty) tys

-- * Invoke the complete System Fc type checker
-- ----------------------------------------------------------------------------

-- Refine the type and also print more stuff out

fcTypeCheck ::
     UniqueSupply
  -> FcProgram
  -> Either CompileError ((FcType, UniqueSupply), FcGblEnv)
fcTypeCheck us pgm = runExcept
                   $ flip runStateT  fc_init_gbl_env
                   $ flip runReaderT fc_init_ctx
                   $ flip runUniqueSupplyT us
                   $ markErrorPhase FcTypeChecker
                   $ do buildInitFcEnv pgm
                        tcFcProgram pgm
  where
    fc_init_ctx     = mempty
    fc_init_gbl_env =
      FcGblEnv
      { fc_env_tc_info = extendAssocList fcArrowTyCon fcArrowTyconInfo mempty
      , fc_env_dc_info = mempty
      , fc_env_tf_info = mempty
      , fc_env_ax_info = mempty
      }

fcFail :: MonadError CompileError m => Doc -> m a
fcFail = throwError . CompileError FcTypeChecker
