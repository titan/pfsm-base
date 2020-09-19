module Pfsm.Checker

import Data.List
import Pfsm
import Pfsm.Data

-------------
-- Utility --
-------------

summary : List (Maybe String) -> Maybe (List String)
summary xs
  = summary' xs []
  where
    summary' : List (Maybe String) -> List String -> Maybe (List String)
    summary' []        []  = Nothing
    summary' []        acc = Just acc
    summary' (x :: xs) acc = case x of
                                  Just x' => summary' xs (x' :: acc)
                                  Nothing => summary' xs acc

---------
-- API --
---------

export
checkersErrorToString : List String -> String
checkersErrorToString = join " "

export
defaultCheckingRules : List (Fsm -> List (Maybe String))
defaultCheckingRules
  = []

export
check : Fsm -> List (Fsm -> List (Maybe String)) -> Either (List String) Fsm
check fsm rules
  = case summary $ foldr (\y, a => y ++ a) [] $ map (\checker => checker fsm) rules of
         Nothing => Right fsm
         Just errs => Left errs
