module Pfsm.FsmLint

import System
import System.File
import Data.List
import public Text.Lexer.Core

import Pfsm
import Pfsm.Analyser
import Pfsm.Checker
import Pfsm.Data
import Pfsm.Parser

lint : String -> IO ()
lint f
  = do Right content <- readFile f
         | Left err => putStrLn $ show err
       case doWork content of
          Left err => putStrLn err
          Right fsm => putStrLn fsm.name
  where
    doWork : String -> Either String Fsm
    doWork content
      = do (sexp, _) <- mapError parseErrorToString $ parseSExp content
           (fsm, _) <- mapError parseErrorToString $ analyse sexp
           fsm' <- mapError checkersErrorToString $ check fsm defaultCheckingRules
           pure fsm'

usage : IO ()
usage = putStrLn "Usage: fsm-lint <FILE>"

main : IO ()
main
  = do
    args <- getArgs
    if length(args) > 1
       then case (last' args) of
                 Nothing => usage
                 Just arg => lint arg
       else usage
