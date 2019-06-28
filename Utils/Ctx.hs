{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances   #-}

module Utils.Ctx
  ( FcTcCtx
  , extendCtxM
  , lookupCtxM
  , notInCtxM
  , setCtxM
  , RnCtx
  , extendCtx
  , lookupCtx
  , TcCtx
  ) where

import           Backend.FcTypes
import           Frontend.HsTypes

import           Utils.Errors
import           Utils.Kind
import           Utils.PrettyPrint
import           Utils.SnocList
import           Utils.Var

import           Control.Monad.Except
import           Control.Monad.Reader

-- * Context operations
-- ------------------------------------------------------------------------------

-- | Context type class
class (Eq src) => Context ctx src trg | src ctx -> trg where
  lookupCtx :: ctx -> src -> Maybe trg
  extendCtx :: ctx -> src -> trg -> ctx

-- | Do a lookup in the context, throw an error if not bound
lookupCtxM ::
     ( MonadError CompileError m
     , PrettyPrint src
     , Context ctx src trg
     , MonadReader ctx m
     )
  => src
  -> m trg
lookupCtxM src = ask >>= \ctx -> case lookupCtx ctx src of
  Just trg -> return trg
  Nothing -> throwErrorM $ text "Unbound variable" <+> colon <+> ppr src

-- | Extend the context
extendCtxM :: (Context ctx src trg, MonadReader ctx m) => src -> trg -> m a -> m a
extendCtxM s t = local (\ctx -> extendCtx ctx s t)

-- | Replace the current context
setCtxM :: MonadReader ctx m => ctx -> m a -> m a
setCtxM ctx = local $ const ctx

-- | Check if something is not already bound in the context, throw an error otherwise
notInCtxM ::
     ( PrettyPrint src
     , MonadReader ctx m
     , MonadError CompileError m
     , Context ctx src trg
     )
  => src
  -> m ()
notInCtxM x = ask >>= \ctx -> case lookupCtx ctx x of
  Just _ -> throwErrorM (text "notInCtxM" <+> colon <+> ppr x <+> text "is already bound")
  Nothing -> return ()

-- | Context instance for lists
instance Context ctx src trg => Context ctx [src] [trg] where
  lookupCtx ctx               = traverse (lookupCtx ctx)
  extendCtx ctx (s:ss) (t:ts) = extendCtx (extendCtx ctx ss ts) s t
  extendCtx ctx []     []     = ctx
  extendCtx _   _      _      = error "extendCtx: length mismatch"
  -- TODO length mismatch, implement als fooM instead for better error?

-- * System Fc typechecker context
-- ------------------------------------------------------------------------------
type FcTcCtx     = SnocList FcTcBinding
data FcTcBinding = FcTcTmBnd FcTmVar FcType
                 | FcTcTyBnd FcTyVar Kind
                 | FcTcCoBnd FcCoVar FcProp

instance Context (SnocList FcTcBinding) FcTmVar FcType where
  lookupCtx (ctx :> FcTcTmBnd a ty) b = if a == b then Just ty else lookupCtx ctx b
  lookupCtx (ctx :> _) b = lookupCtx ctx b
  lookupCtx SN _ = Nothing
  extendCtx ctx src trg = ctx :> FcTcTmBnd src trg

instance Context (SnocList FcTcBinding) FcTyVar Kind where
  lookupCtx (ctx :> FcTcTyBnd a k) b = if a == b then Just k else lookupCtx ctx b
  lookupCtx (ctx :> _) b = lookupCtx ctx b
  lookupCtx SN _ = Nothing
  extendCtx ctx src trg = ctx :> FcTcTyBnd src trg

instance Context (SnocList FcTcBinding) FcCoVar FcProp where
  lookupCtx (ctx :> FcTcCoBnd a phi) b = if a == b then Just phi else lookupCtx ctx b
  lookupCtx (ctx :> _) b = lookupCtx ctx b
  lookupCtx SN _ = Nothing
  extendCtx ctx src trg = ctx :> FcTcCoBnd src trg

-- * Renamer context
-- ------------------------------------------------------------------------------
type RnCtx = SnocList RnBinding
data RnBinding = RnTmVarBnd PsTmVar RnTmVar
               | RnTyVarBnd PsTyVar RnTyVar

instance Context RnCtx PsTmVar RnTmVar where
  lookupCtx (ctx :> RnTmVarBnd a a') b = if a == b then Just a' else lookupCtx ctx b
  lookupCtx (ctx :> _) b = lookupCtx ctx b
  lookupCtx SN _ = Nothing
  extendCtx ctx src trg = ctx :> RnTmVarBnd src trg

instance Context RnCtx PsTyVar RnTyVar where
  lookupCtx (ctx :> RnTyVarBnd a a') b = if a == b then Just a' else lookupCtx ctx b
  lookupCtx (ctx :> _) b = lookupCtx ctx b
  lookupCtx SN _ = Nothing
  extendCtx ctx src trg = ctx :> RnTyVarBnd src trg

-- * Haskell typechecker context
-- ------------------------------------------------------------------------------
type TcCtx = SnocList TcBinding
data TcBinding = TcTmVarBnd RnTmVar RnPolyTy
               | TcTyVarBnd RnTyVar Kind

instance Context TcCtx RnTmVar RnPolyTy where
  lookupCtx (ctx :> TcTmVarBnd a ty) b = if a == b then Just ty else lookupCtx ctx b
  lookupCtx (ctx :> _) b = lookupCtx ctx b
  lookupCtx SN _ = Nothing
  extendCtx ctx src trg = ctx :> TcTmVarBnd src trg

instance Context TcCtx RnTyVar Kind where
  lookupCtx (ctx :> TcTyVarBnd a k) b = if a == b then Just k else lookupCtx ctx b
  lookupCtx (ctx :> _) b = lookupCtx ctx b
  lookupCtx SN _ = Nothing
  extendCtx ctx src trg = ctx :> TcTyVarBnd src trg
