{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE UndecidableInstances   #-} -- should be fine

-- Quick fix for https://prime.haskell.org/wiki/Libraries/Proposals/MonadFail
-- Doesn't work well with type alias monad stacks.
{-# OPTIONS_GHC -fno-warn-orphans   #-}

module Utils.Errors where

import Utils.PrettyPrint

import Control.Monad.Except
import Control.Monad.Fail

throwErrorM :: MonadError CompileError m => Doc -> m a
throwErrorM = throwError . CompileError Unknown

data CompilePhase
  = HsParser
  | HsRenamer
  | HsTypeChecker
  | FcTypeChecker
  | Unknown
  deriving (Show)

data CompileError = CompileError CompilePhase Doc

instance (Monad m, MonadError CompileError m) => MonadFail m where
  fail = throwError . CompileError Unknown . text

throwMainError :: CompileError -> IO ()
throwMainError (CompileError phase e) = putStrLn (renderWithColor msg)
  where
    label = colorDoc red (text (show phase) <+> text "failure")
    msg = brackets label <+> colorDoc red e

markErrorPhase :: MonadError CompileError m => CompilePhase -> m a -> m a
markErrorPhase phase f =
  f `catchError`
  (\(CompileError _phase err) -> throwError (CompileError phase err))
