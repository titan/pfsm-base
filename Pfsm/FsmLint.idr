module Main

import System
import System.File
import Data.List
import public Text.Lexer.Core

import Pfsm.Analyser
import Pfsm.Data
import Pfsm.Parser
import Pfsm.Checker

lint : String -> IO ()
lint f
  = do
    r <- readFile f
    case r of
         Left e => putStrLn $ show e
         Right content => case parseSExp content of
                               Left (Error e r) => putStrLn ("Parse error " ++ e)
                               Right (sexp, _) => case analyse sexp of
                                                       Left (Error e _) => putStrLn $ "run analyser error, " ++ e
                                                       Right (fsm, _) => case check fsm defaultCheckingRules of
                                                                              Just errs => putStrLn $ foldr (\x, a => x ++ "\n" ++ a) "" errs
                                                                              Nothing => putStrLn (fsm.name ++ " is okay")

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
