{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeSynonymInstances       #-}
{-# LANGUAGE UndecidableInstances       #-}

module Backend.FcTypes where

import Utils.Unique
import Utils.Var
import Utils.Kind
import Utils.PrettyPrint
import Utils.Annotated

import Data.Maybe (isJust)
import Data.Function (on)
import Data.Semigroup

-- * Arrow Type Constructor
-- ----------------------------------------------------------------------------

mkFcArrowTy :: FcType -> FcType -> FcType
mkFcArrowTy ty1 ty2 = FcTyApp (FcTyApp (FcTyCon fcArrowTyCon) ty1) ty2

fcArrowTyCon :: FcTyCon
fcArrowTyCon = FcTC (mkName (mkSym "(->)") arrowTyConUnique)

fcArrowTyconInfo :: FcTyConInfo
fcArrowTyconInfo =
  FcTCInfo
    fcArrowTyCon
    [ mkFcTyVar (mkName (mkSym "a") arrowTyVar1Unique) KStar
    , mkFcTyVar (mkName (mkSym "b") arrowTyVar2Unique) KStar
    ]

isFcArrowTy :: FcType -> Maybe (FcType, FcType)
isFcArrowTy (FcTyApp (FcTyApp (FcTyCon tc) ty1) ty2)
  | tc == fcArrowTyCon  = Just (ty1, ty2)
isFcArrowTy _other_type = Nothing

-- * Types
-- ----------------------------------------------------------------------------
data FcType = FcTyVar FcTyVar        -- ^ Type variable
            | FcTyAbs FcTyVar FcType -- ^ Type abstraction
            | FcTyApp FcType  FcType -- ^ Type application
            | FcTyCon FcTyCon        -- ^ Type constructor
            | FcTyQual FcProp FcType -- ^ psi => v
            | FcTyFam FcTyFam [FcType] -- ^ F(vs)

data FcProp = FcProp FcType FcType -- ^ Type equality proposition -- v_1 ~ v_2

data FcCoercion = FcCoVar FcCoVar -- ^ c
                | FcCoAx FcAxVar [FcType] -- ^ g vs
                | FcCoRefl FcType -- ^ <v>
                | FcCoSym FcCoercion -- ^ sym gamma
                | FcCoTrans FcCoercion FcCoercion -- ^ gamma_1 ; gamma_2
                | FcCoApp FcCoercion FcCoercion -- ^ gamma_1 gamma_2
                | FcCoLeft FcCoercion -- ^ left gamma
                | FcCoRight FcCoercion -- ^ right gamma
                | FcCoFam FcTyFam [FcCoercion] -- ^ F(gammas)
                | FcCoAbs FcTyVar FcCoercion -- ^ forall a. gamma
                | FcCoInst FcCoercion FcCoercion -- ^ gamma_1 [gamma_2]
                | FcCoQual FcProp FcCoercion -- ^ psi => gamma
                | FcCoQInst FcCoercion FcCoercion -- ^ gamma_1 @ gamma_2

-- | Syntactic equality on System F types
eqFcTypes :: FcType -> FcType -> Bool
eqFcTypes (FcTyVar v1)    (FcTyVar v2)    = v1 == v2
eqFcTypes (FcTyAbs v1 t1) (FcTyAbs v2 t2) = (v1 == v2)      && eqFcTypes t1 t2
eqFcTypes (FcTyApp t1 t2) (FcTyApp t3 t4) = eqFcTypes t1 t3 && eqFcTypes t2 t4
eqFcTypes (FcTyCon tc1)   (FcTyCon tc2)   = tc1 == tc2
eqFcTypes (FcTyQual p1 t1) (FcTyQual p2 t2) = eqFcTypes t1 t2 && eqFcProp p1 p2
eqFcTypes (FcTyFam f1 ts1) (FcTyFam f2 ts2) =
  and (zipWith eqFcTypes ts1 ts2) && f1 == f2

eqFcTypes (FcTyVar  {}) _ = False
eqFcTypes (FcTyAbs  {}) _ = False
eqFcTypes (FcTyApp  {}) _ = False
eqFcTypes (FcTyCon  {}) _ = False
eqFcTypes (FcTyQual {}) _ = False
eqFcTypes (FcTyFam  {}) _ = False

-- | Syntactic equality on System Fc propositions
eqFcProp :: FcProp -> FcProp -> Bool
eqFcProp (FcProp ty1 ty2) (FcProp ty3 ty4) =
  eqFcTypes ty1 ty3 && eqFcTypes ty2 ty4

-- | Type Constructors
newtype FcTyCon = FcTC { unFcTC :: Name }

instance Eq FcTyCon where
  (==) = (==) `on` unFcTC

instance Ord FcTyCon where
  compare = compare `on` unFcTC

instance Symable FcTyCon where
  symOf = symOf . unFcTC

instance Named FcTyCon where
  nameOf = unFcTC

instance Uniquable FcTyCon where
  getUnique = getUnique . unFcTC

data FcTyConInfo
  = FcTCInfo { fc_tc_ty_con    :: FcTyCon     -- ^ The type constructor name
             , fc_tc_type_args :: [FcTyVar] } -- ^ Universal types

-- | Pretty print type constructor info
instance PrettyPrint FcTyConInfo where
  ppr (FcTCInfo tc type_args)
    = braces $ vcat $ punctuate comma
    $ [ text "fc_tc_ty_con"    <+> colon <+> ppr tc
      , text "fc_tc_type_args" <+> colon <+> ppr type_args
      ]

  needsParens _ = False

-- | Data Constructors
newtype FcDataCon = FcDC { unFcDC :: Name }
  deriving (Eq, Ord)

instance Symable FcDataCon where
  symOf = symOf . unFcDC

instance Named FcDataCon where
  nameOf = unFcDC

instance Uniquable FcDataCon where
  getUnique = getUnique . unFcDC

data FcDataConInfo
  = FcDCInfo { fc_dc_data_con :: FcDataCon  -- ^ The data constructor name
             , fc_dc_univ     :: [FcTyVar]  -- ^ Universal type variables
             , fc_dc_exis     :: [FcTyVar]  -- ^ Existantial type variables
             , fc_dc_prop     :: [FcProp]   -- ^ Coercion proposition
             , fc_dc_parent   :: FcTyCon    -- ^ Parent type constructor
             , fc_dc_arg_tys  :: [FcType] } -- ^ Argument types

-- | Pretty print data constructor info
instance PrettyPrint FcDataConInfo where
  ppr (FcDCInfo dc univ exis prop tc arg_tys)
    = braces $ vcat $ punctuate comma
    $ [ text "fc_dc_data_con" <+> colon <+> ppr dc
      , text "fc_dc_univ"     <+> colon <+> ppr univ
      , text "fc_dc_exis"     <+> colon <+> ppr exis
      , text "fc_dc_prop"     <+> colon <+> ppr prop
      , text "fc_dc_parent"   <+> colon <+> ppr tc
      , text "fc_dc_arg_tys"  <+> colon <+> ppr arg_tys
      ]
  needsParens _ = False

-- | Type Families
newtype FcTyFam = FcTF { unFcTF :: Name }
  deriving (Eq, Ord, Symable, Named, Uniquable)

data FcFamInfo = FcFamInfo
  { fc_fam_var  :: FcTyFam
  , fc_fam_univ :: [FcTyVar]
  , fc_fam_kind :: Kind
  }

instance PrettyPrint FcFamInfo where
  ppr (FcFamInfo f as _k) =
    braces $ vcat $ punctuate comma $
      [ text "fc_fam_var"  <+> colon <+> ppr f
      , text "fc_fam_univ" <+> colon <+> ppr as
      ]
  needsParens _ = False

-- | Coercion variables
newtype FcCoVar = FcCV { unFcCV :: Name }
  deriving (Eq, Ord, Symable, Named, Uniquable)

freshFcCoVar :: MonadUnique m => m FcCoVar
freshFcCoVar = FcCV . mkName (mkSym "c") <$> getUniqueM

data FcCoInfo = FcCoInfo
  { fc_co_var :: FcCoVar
  , fc_co_val :: FcCoercion
  }

newtype FcAxVar = FcAV { unFcAV :: Name }
  deriving (Eq, Ord, Symable, Named, Uniquable)

freshFcAxVar :: MonadUnique m => m FcAxVar
freshFcAxVar = FcAV . mkName (mkSym "g") <$> getUniqueM

data FcAxiomInfo = FcAxiomInfo
  { fc_ax_var  :: FcAxVar   -- ^ g
  , fc_ax_uv  :: [FcTyVar] -- ^ Universal Type variables -- as
  , fc_ax_fv  :: FcTyFam  -- ^ Type Family -- F
  , fc_ax_fvs :: [FcType] -- ^ Type Family type arguments -- us
  , fc_ax_ty  :: FcType    -- ^ Equal Type -- v
  }

axiomToProp :: FcAxiomInfo -> FcProp
axiomToProp (FcAxiomInfo _g _as f us v) =
  FcProp (FcTyFam f us) v

instance PrettyPrint FcAxiomInfo where
  ppr (FcAxiomInfo g as f us v) =
    braces $ vcat $ punctuate comma $
      [ text "fc_ax_var" <+> colon <+> ppr g
      , text "fc_ax_uv"   <+> colon <+> ppr as
      , text "fc_ax_fv"   <+> colon <+> ppr f
      , text "fc_ax_fvs"   <+> colon <+> ppr us
      , text "fc_ax_ty"   <+> colon <+> ppr v
      ]
  needsParens _ = False

-- -- | Take the type apart the hindley milner way
-- destructFcTypeHM :: FcType -> ([FcTyVar], [FcType], FcType)
-- destructFcTypeHM (FcTyArr ty1 ty2) = (as, ty1:lhs, rhs)
--   where (as, lhs, rhs) = destructFcTypeHM ty2
-- destructFcTypeHM (FcTyAbs a ty) = (a:as, lhs, rhs)
--   where (as, lhs, rhs) = destructFcTypeHM ty
-- destructFcTypeHM ty@(FcTyVar  {}) = ([], [], ty)
-- destructFcTypeHM ty@(FcTyApp  {}) = ([], [], ty)
-- destructFcTypeHM ty@(FcTyCon  {}) = ([], [], ty)

constructFcTypeHM :: ([FcTyVar], [FcType], FcType) -> FcType
constructFcTypeHM (as, tys, ty) = fcTyAbs as (fcTyArr tys ty)

-- | Take apart a type constructor application
tyConAppMaybe :: FcType -> Maybe (FcTyCon, [FcType])
tyConAppMaybe ty = go ty []
  where
    go :: FcType -> [FcType] -> Maybe (FcTyCon, [FcType])
    go (FcTyApp ty1 ty2)  tys = go ty1 (ty2:tys)
    go (FcTyCon tc)       tys = Just (tc, tys)
    go _other_ty         _tys = Nothing

constructFcDCType :: ([FcTyVar], [FcProp], [FcType], FcTyCon, [FcTyVar]) -> FcType
constructFcDCType (bs, psis, tys, tc, as) =
  fcTyAbs (as `mappend` bs) $
  fcTyQual psis $ fcTyArr tys $ fcTyApp (FcTyCon tc) $ map FcTyVar as

-- * Some smart constructors (uncurried variants)
-- ----------------------------------------------------------------------------

-- | Uncurried version of data constructor FcTyAbs
fcTyAbs :: [FcTyVar] -> FcType -> FcType
fcTyAbs vars ty = foldr FcTyAbs ty vars

-- | Uncurried version of data constructor FcTyArr
fcTyArr :: [FcType] -> FcType -> FcType
fcTyArr tys ty = foldr mkFcArrowTy ty tys

-- | Uncurried version of data constructor FcTyApp
fcTyApp :: FcType -> [FcType] -> FcType
fcTyApp ty tys = foldl FcTyApp ty tys

-- | Apply a type constructor to a bunch of types
fcTyConApp :: FcTyCon -> [FcType] -> FcType
fcTyConApp tc tys = fcTyApp (FcTyCon tc) tys

-- | Uncurried version of data contructor FcTyQual
fcTyQual :: [FcProp] -> FcType -> FcType
fcTyQual psis ty = foldr FcTyQual ty psis

-- * Terms
-- ----------------------------------------------------------------------------
data FcTerm = FcTmAbs FcTmVar FcType FcTerm         -- ^ Term abstraction: lambda x : ty . tm
            | FcTmVar FcTmVar                       -- ^ Term variable
            | FcTmApp FcTerm FcTerm                 -- ^ Term application
            | FcTmTyAbs FcTyVar FcTerm              -- ^ Type abstraction: Lambda a . tm
            | FcTmTyApp FcTerm FcType               -- ^ Type application
            | FcTmDataCon FcDataCon                 -- ^ Data constructor
            | FcTmLet FcTmVar FcType FcTerm FcTerm  -- ^ Let binding: let x : ty = tm in tm
            | FcTmCase FcTerm [FcAlt]               -- ^ Case
            | FcTmPropAbs FcCoVar FcProp FcTerm     -- ^ Lambda(c : psi). t
            | FcTmCoApp FcTerm FcCoercion           -- ^ t gamma
            | FcTmCast FcTerm FcCoercion            -- ^ t > gamma

-- You should never need to make terms and patterns instances of Eq. If
-- you do it means that something is probably wrong (the only setting where you
-- need stuff like this is for optimizations).

-- | Patterns
data FcPat =
  FcConPat FcDataCon            -- K
           [FcTyVar]            -- ^ bs
           [Ann FcCoVar FcProp] -- ^ (c : psi)s
           [Ann FcTmVar FcType] -- ^ (d : tau)s (f : v  )s

-- | Case alternative(s)
data FcAlt  = FcAlt FcPat FcTerm
type FcAlts = [FcAlt]

-- * Dictionary Contexts
-- ----------------------------------------------------------------------------

data DictCtx = HoleCtx                               -- ^ Hole: []
             | LetCtx FcTmVar FcType FcTerm DictCtx  -- ^ Let binding: let x : ty = tm in tm

-- | Apply a dictionary context to a term
applyDictCtx :: DictCtx -> FcTerm -> FcTerm
applyDictCtx HoleCtx               tm2 = tm2
applyDictCtx (LetCtx x ty tm1 ctx) tm2 = FcTmLet x ty tm1 (applyDictCtx ctx tm2)

instance Semigroup DictCtx where
  (<>) = mappend

-- | Dictionary contexts are monoidal (if we ignore their well-scopedness)
instance Monoid DictCtx where
  mempty = HoleCtx
  mappend HoleCtx               ctx2 = ctx2
  mappend (LetCtx x ty tm ctx1) ctx2 = LetCtx x ty tm (mappend ctx1 ctx2)

-- * Some smart constructors (uncurried variants)
-- ----------------------------------------------------------------------------

-- | Uncurried version of data constructor FcTmAbs
fcTmAbs :: [(FcTmVar, FcType)] -> FcTerm -> FcTerm
fcTmAbs binds tm = foldr (uncurry FcTmAbs) tm binds

-- | Uncurried version of data constructor FcTmTyAbs
fcTmTyAbs :: [FcTyVar] -> FcTerm -> FcTerm
fcTmTyAbs tvs tm = foldr FcTmTyAbs tm tvs

-- | Uncurried version of data constructor FcTmApp
fcTmApp :: FcTerm -> [FcTerm] -> FcTerm
fcTmApp tm tms = foldl FcTmApp tm tms

-- | Uncurried version of data constructor FcTmTyApp
fcTmTyApp :: FcTerm -> [FcType] -> FcTerm
fcTmTyApp tm tys = foldl FcTmTyApp tm tys

-- | Create a data constructor application
fcDataConApp :: FcDataCon -> FcType -> [FcTerm] -> FcTerm
fcDataConApp dc ty = fcTmApp (FcTmTyApp (FcTmDataCon dc) ty)

-- | Apply a term to a list of dictionary variables
fcDictApp :: FcTerm -> [DictVar] -> FcTerm
fcDictApp tm ds = foldl FcTmApp tm (map FcTmVar ds)

-- * Programs and declarations
-- ----------------------------------------------------------------------------

-- | Data Type Declaration
data FcDataDecl = FcDataDecl { fdata_decl_tc   :: FcTyCon                 -- ^ Type Constructor
                             , fdata_decl_tv   :: [FcTyVar]               -- ^ Universal Type variables
                             , fdata_decl_cons :: [(FcDataCon, [FcTyVar], [FcProp], [FcType])] -- ^ Data Constructors
                             } -- FIXME decl_cons dirty

-- | Top-level Value Binding
data FcValBind = FcValBind { fval_bind_var :: FcTmVar   -- ^ Variable Name
                           , fval_bind_ty  :: FcType    -- ^ Variable Type
                           , fval_bind_tm  :: FcTerm    -- ^ Variable Value
                           }

data FcFamDecl = FcFamDecl FcTyFam [FcTyVar] Kind -- type F(as)

data FcAxiomDecl = FcAxiomDecl -- g as : F(us) ~ v
  { fax_decl_vr  :: FcAxVar    -- ^ Axiom variable             -- g
  , fax_decl_tv  :: [FcTyVar]  -- ^ Universal Type variables   -- as
  , fax_decl_fv  :: FcTyFam    -- ^ Type Family                -- F
  , fax_decl_fvs :: [FcType]   -- ^ Type Family type arguments -- us
  , fax_decl_ty  :: FcType     -- ^ Equal Type                 -- v
  }

-- | Program
data FcProgram = FcPgmDataDecl FcDataDecl FcProgram     -- ^ Data Declaration
               | FcPgmValDecl  FcValBind  FcProgram     -- ^ Value Binding
               | FcPgmTerm FcTerm                       -- ^ Term
               | FcPgmAxiomDecl FcAxiomDecl FcProgram   -- ^ Axiom Declaration
               | FcPgmFamDecl FcFamDecl FcProgram       -- ^ Type Family Declaration

-- * Pretty printing
-- ----------------------------------------------------------------------------

isFcTyApp :: FcType -> Bool
isFcTyApp (FcTyApp {}) = True
isFcTyApp _other       = False

isFcTyAbs :: FcType -> Bool
isFcTyAbs (FcTyAbs {}) = True
isFcTyAbs _other       = False

-- | Pretty print types
instance PrettyPrint FcType where
  ppr ty | Just (ty1, ty2) <- isFcArrowTy ty
         , let d1 = if isJust (isFcArrowTy ty1) || isFcTyAbs ty1
                      then pprPar ty1
                      else ppr ty1
         , let d2 = if isJust (isFcArrowTy ty2) || isFcTyApp ty2
                      then ppr ty2
                      else pprPar ty2
         = d1 <+> arrow <+> d2

  ppr (FcTyVar a)       = ppr a
  ppr (FcTyAbs a ty)    = text "forall" <+> ppr a <> dot <+> ppr ty
  ppr (FcTyApp ty1 ty2)
    | FcTyApp {} <- ty1 = ppr ty1    <+> pprPar ty2
    | otherwise         = pprPar ty1 <+> pprPar ty2
  ppr (FcTyCon tc)      = ppr tc
  ppr (FcTyQual psi ty) = ppr psi <+> darrow <+> ppr ty
  ppr (FcTyFam f tys) = ppr f <> parens (sep (punctuate comma (map ppr tys)))

  needsParens (FcTyApp  {}) = True
  needsParens (FcTyAbs  {}) = True
  needsParens (FcTyVar  {}) = False
  needsParens (FcTyCon  {}) = False
  needsParens (FcTyQual {}) = True
  needsParens (FcTyFam  {}) = False

-- | Pretty print type constructors
instance PrettyPrint FcTyCon where
  ppr           = ppr . symOf -- Do not show the uniques on the constructors
  needsParens _ = False

-- | Pretty print data constructors
instance PrettyPrint FcDataCon where
  ppr           = ppr . symOf -- Do not show the uniques on the constructors
  needsParens _ = False

-- | Pretty print terms
instance PrettyPrint FcTerm where
  ppr (FcTmAbs x ty tm)    = hang (backslash <> parens (ppr x <+> dcolon <+> ppr ty) <> dot) 2 (ppr tm)
  ppr (FcTmVar x)          = ppr x
  ppr (FcTmApp tm1 tm2)
    | FcTmApp   {} <- tm1  = ppr tm1    <+> pprPar tm2
    | FcTmTyApp {} <- tm1  = ppr tm1    <+> pprPar tm2
    | otherwise            = pprPar tm1 <+> pprPar tm2
  ppr (FcTmTyAbs a tm)     = hang (colorDoc yellow (text "/\\") <> ppr a <> dot) 2 (ppr tm)
  ppr (FcTmTyApp tm ty)    = pprPar tm <+> brackets (ppr ty)
  ppr (FcTmDataCon dc)     = ppr dc
  ppr (FcTmLet x ty tm1 tm2)
    =  (colorDoc yellow (text "let") <+> ppr x <+> ((colon <+> ppr ty) $$ (equals <+> ppr tm1)))
    $$ (colorDoc yellow (text "in" ) <+> ppr tm2)

  ppr (FcTmCase tm cs)     = hang (colorDoc yellow (text "case") <+> ppr tm <+> colorDoc yellow (text "of"))
                                  2 (vcat $ map ppr cs)
  ppr (FcTmPropAbs c psi tm) =
    parens (ppr c <+> colon <+> ppr psi) <> dot <+> ppr tm
  ppr (FcTmCoApp tm co) = ppr tm <+> ppr co
  ppr (FcTmCast tm co) = ppr tm <+> text ">" <+> ppr co

  needsParens (FcTmApp     {}) = True
  needsParens (FcTmTyApp   {}) = True
  needsParens (FcTmLet     {}) = True
  needsParens (FcTmCase    {}) = True
  needsParens (FcTmAbs     {}) = True
  needsParens (FcTmVar     {}) = False
  needsParens (FcTmTyAbs   {}) = True
  needsParens (FcTmDataCon {}) = False
  needsParens (FcTmPropAbs {}) = True
  needsParens (FcTmCoApp   {}) = True
  needsParens (FcTmCast    {}) = True

-- | Pretty print patterns
instance PrettyPrint FcPat where
  ppr (FcConPat dc bs cs vs) =
    ppr dc <+> hsep (ppr <$> bs) <+> hsep (ppr <$> cs) <+> hsep (ppr <$> vs)
  needsParens _        = True

-- | Pretty print case alternatives
instance PrettyPrint FcAlt where
  ppr (FcAlt p tm) = ppr p <+> arrow <+> ppr tm
  needsParens _    = True

-- | Pretty print data declarations
instance PrettyPrint FcDataDecl where
  ppr (FcDataDecl tc as dcs) =
   hang data_ty_decl 2 . vcat $ map ppr_dc dcs
    where
      data_ty_decl =
        hsep
          [ colorDoc green (text "data")
          , ppr tc
          , hsep (ppr <$> ann_as)
          , colorDoc green (text "where")
          ]

      ann_as = map (\a -> (a :| kindOf a)) as

      ppr_dc (dc, bs, psis, tys) =
        hsep [ppr dc, dcolon, ppr (constructFcDCType (bs, psis, tys, tc, as))]

  needsParens _ = False

-- | Pretty print top-level value bindings
instance PrettyPrint FcValBind where
  ppr (FcValBind x ty tm) = hsep [ colorDoc yellow (text "let"), ppr x
                                 , vcat [ colon <+> ppr ty, equals <+> ppr tm ]
                                 ]
  needsParens _ = False

-- | Pretty print programs
instance PrettyPrint FcProgram where
  ppr (FcPgmDataDecl datadecl pgm) = ppr datadecl $$ ppr pgm
  ppr (FcPgmValDecl  valbind  pgm) = ppr valbind  $$ ppr pgm
  ppr (FcPgmFamDecl famdecl pgm)   = ppr famdecl  $$ ppr pgm
  ppr (FcPgmAxiomDecl axdecl pgm)  = ppr axdecl   $$ ppr pgm
  ppr (FcPgmTerm tm)               = ppr tm
  needsParens _ = False

-- | Pretty print a proposition
instance PrettyPrint FcProp where
  ppr (FcProp ty1 ty2) = ppr ty1 <+> text "~" <+> ppr ty2
  needsParens _        = True

-- | Pretty print a type family
instance PrettyPrint FcTyFam where
  ppr           = ppr . symOf
  needsParens _ = False

-- | Pretty print a coercion variable
instance PrettyPrint FcCoVar where
  ppr           = ppr . unFcCV
  needsParens _ = False

-- | Pretty print an axiom variable
instance PrettyPrint FcAxVar where
  ppr           = ppr . unFcAV
  needsParens _ = False

-- | Pretty print coercions
instance PrettyPrint FcCoercion where
  ppr (FcCoVar c) = ppr c
  ppr (FcCoAx g tys) = ppr g <+> sep (map ppr tys)
  ppr (FcCoRefl ty) = text "<" <> ppr ty <> text ">"
  ppr (FcCoSym co) = text "sym" <+> ppr co
  ppr (FcCoTrans co1 co2) = ppr co1 <> text ";" <+> ppr co2
  ppr (FcCoApp co1 co2) = ppr co1 <+> ppr co2
  ppr (FcCoLeft co) = text "left" <+> ppr co
  ppr (FcCoRight co) = text "right" <+> ppr co
  ppr (FcCoFam f crcs) = ppr f <> parens (sep (punctuate comma (map ppr crcs)))
  ppr (FcCoAbs a co) = text "forall" <+> ppr a <> dot <+> ppr co
  ppr (FcCoInst co1 co2) = ppr co1 <+> brackets (ppr co2)
  ppr (FcCoQual psi co) = ppr psi <+> darrow <+> ppr co
  ppr (FcCoQInst co1 co2) = ppr co1 <+> text "@" <+> ppr co2

  needsParens (FcCoVar {})   = False
  needsParens (FcCoAx {})    = True
  needsParens (FcCoRefl {})  = False
  needsParens (FcCoSym {})   = True
  needsParens (FcCoTrans {}) = False
  needsParens (FcCoApp {})   = True
  needsParens (FcCoLeft {})  = True
  needsParens (FcCoRight {}) = True
  needsParens (FcCoFam {})   = False
  needsParens (FcCoAbs {})   = True
  needsParens (FcCoInst {})  = False
  needsParens (FcCoQual {})  = True
  needsParens (FcCoQInst {}) = True

-- | Pretty print family declarations
instance PrettyPrint FcFamDecl where
  ppr (FcFamDecl f as _k) =
    colorDoc green (text "type") <+>
    ppr f <> parens (sep (punctuate comma (map ppr as)))
  needsParens _ = False

-- | Pretty print axiom declarations
instance PrettyPrint FcAxiomDecl where
  ppr (FcAxiomDecl g as f us v) =
    colorDoc green (text "axiom") <+>
    ppr g <+>
      parens (sep (punctuate comma (map ppr as))) <+>
      colon <+>
      ppr f <> parens (sep (punctuate comma (map ppr us))) <+>
      text "~" <+>
      ppr v
  needsParens _ = False
