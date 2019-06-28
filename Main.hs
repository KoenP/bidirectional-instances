{-# LANGUAGE LambdaCase #-}

module Main
  ( main
  , runTest
  ) where

import           Backend.FcTypeChecker  (fcTypeCheck)
import           Frontend.HsParser      (hsParse)
import           Frontend.HsRenamer     (hsRename)
import           Frontend.HsTypeChecker (hsElaborate)

import           Utils.Errors
import           Utils.PrettyPrint
import           Utils.Unique           (newUniqueSupply)

import           System.Environment     (getArgs, getProgName)

main :: IO ()
main =
  getArgs >>= \case
    [filename] -> runTest filename
    _other -> do
      progName <- getProgName
      putStrLn $ concat ["Usage: ", progName, " <filename>"]

-- | Run a single testfile
runTest :: FilePath -> IO ()
runTest filePath = do
  us0 <- newUniqueSupply 'u'
  fileContents <- readFile filePath
  let result = do
        ps_pgm <- hsParse fileContents filePath
        (((rn_pgm, _rn_ctx), us1), rn_env) <- hsRename us0 ps_pgm
        (((fc_pgm, tc_ty, theory), us2), _tc_env) <-
          hsElaborate rn_env us1 rn_pgm
        ((fc_ty, _us3), _fc_env) <- fcTypeCheck us2 fc_pgm
        return (fc_pgm, tc_ty, theory, fc_ty)
  case result of
    Left err -> throwMainError err
    Right (fc_pgm, tc_ty, theory, fc_ty) -> do
      putStrLn
        "---------------------------- Elaborated Program ---------------------------"
      putStrLn $ renderWithColor $ ppr fc_pgm
      putStrLn
        "------------------------------- Program Type ------------------------------"
      putStrLn $ renderWithColor $ ppr tc_ty
      putStrLn
        "------------------------------ Program Theory -----------------------------"
      putStrLn $ renderWithColor $ ppr theory
      putStrLn
        "-------------------------- System Fc Program Type -------------------------"
      putStrLn $ renderWithColor $ ppr fc_ty
