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
defaultCheckingRules : List (Fsm -> List (Maybe String))
defaultCheckingRules
  = []

export
check : Fsm -> List (Fsm -> List (Maybe String)) -> Maybe (List String)
check fsm rules
  = summary $ foldr (\y, a => y ++ a) [] $ map (\x => x fsm) rules
