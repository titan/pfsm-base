module Pfsm.Checker

import Data.List
import Data.List1
import Data.SortedMap
import Data.String.Extra
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

-------------
-- Checker --
-------------

checkOutputActionPorts : Fsm -> List (Maybe String)
checkOutputActionPorts fsm
  = let env = rootEnv fsm
        serrs = map (checkOutputActionPortOfState env) $ List1.toList fsm.states
        terrs = map (checkOutputActionPortOfTransition env) $ List1.toList fsm.transitions in
        List.flatten $ serrs ++ terrs
  where
    checkOutputActionPortType : SortedMap Expression Tipe -> Tipe -> List Expression -> Maybe String
    checkOutputActionPortType env TUnit              []                                  = Nothing
    checkOutputActionPortType env TUnit              (x :: xs)                           = Just ("Parameter type mismatch")
    checkOutputActionPortType env (TArrow tsrc tdst) []                                  = Just ("Parameter type mismatch")
    checkOutputActionPortType env (TArrow tsrc tdst) ((ApplicationExpression _ _) :: xs) = checkOutputActionPortType env tdst xs
    checkOutputActionPortType env (TArrow tsrc tdst) (x :: xs)                           = case inferType env x of
                                                                                                Just t => if tsrc == t
                                                                                                             then checkOutputActionPortType env tdst xs
                                                                                                             else Just ("Parameter type mismatch, from " ++ (show tsrc) ++ " to " ++ (show x) ++ ",")
                                                                                                _ => checkOutputActionPortType env tdst xs
    checkOutputActionPortType env _                  _                                   = Just ("Parameter type mismatch")

    checkOutputActionPort : SortedMap Expression Tipe -> Action -> Maybe String
    checkOutputActionPort env (AssignmentAction _ _)              = Nothing
    checkOutputActionPort env oa@(OutputAction (MkPort pn pt) es) = map (\x => x ++ " in " ++ (show oa)) $ checkOutputActionPortType env pt es

    checkOutputActionPortOfState : SortedMap Expression Tipe -> State -> List (Maybe String)
    checkOutputActionPortOfState env (MkState _ (Just enas) (Just exas) _)
      = let enoas = filter outputActionFilter enas
            exoas = filter outputActionFilter exas in
            map (checkOutputActionPort env) (enoas ++ exoas)
    checkOutputActionPortOfState env (MkState _ (Just as) Nothing _)
      = let oas = filter outputActionFilter as in
            map (checkOutputActionPort env) oas
    checkOutputActionPortOfState env (MkState _ Nothing (Just as) _)
      = let oas = filter outputActionFilter as in
            map (checkOutputActionPort env) oas
    checkOutputActionPortOfState env (MkState _ Nothing Nothing _)
      = []

    checkOutputActionPortOfTransition : SortedMap Expression Tipe -> Transition -> List (Maybe String)
    checkOutputActionPortOfTransition env (MkTransition _ _ ts)
      = List.flatten $ map (checkOutputActionPortOfTrigger env) $ List1.toList ts
      where
        checkOutputActionPortOfTrigger : SortedMap Expression Tipe -> Trigger -> List (Maybe String)
        checkOutputActionPortOfTrigger env (MkTrigger _ (MkEvent _ ps _) _ (Just as))
          = let env' = foldl (\acc, (n, t, _) => insert (IdentifyExpression ("@" ++ n)) t acc) env ps
                oas = filter outputActionFilter as in
                map (checkOutputActionPort env) oas
        checkOutputActionPortOfTrigger env (MkTrigger _ (MkEvent _ ps _) _ Nothing)
          = []

---------
-- API --
---------

export
checkersErrorToString : List String -> String
checkersErrorToString = List.join "\n"

export
defaultCheckingRules : List (Fsm -> List (Maybe String))
defaultCheckingRules
  = [ checkOutputActionPorts ]

export
check : Fsm -> List (Fsm -> List (Maybe String)) -> Either (List String) Fsm
check fsm rules
  = case summary $ foldr (\y, a => y ++ a) [] $ map (\checker => checker fsm) rules of
         Nothing => Right fsm
         Just errs => Left errs
