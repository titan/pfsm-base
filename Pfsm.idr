module Pfsm

import Data.List
import Data.List1
import Data.SortedMap
import Data.SortedSet
import Data.Strings
import Data.Vect

import Pfsm.Data

-------------
-- Utility --
-------------

export
repeat : String -> Nat -> String
repeat str cnt
  = repeat' "" str cnt
  where
    repeat' : String -> String -> Nat -> String
    repeat' acc _   0   = acc
    repeat' acc str cnt = repeat' (acc ++ str) str (minus cnt 1)

export
indent : Nat -> String
indent idt = repeat " " idt

export
nonblank : String -> Bool
nonblank s = length s > Z

namespace Pfsm.Data.Meta
  export
  lookup : MetaKey -> Maybe (List Meta) -> Maybe MetaValue
  lookup k Nothing   = Nothing
  lookup k (Just ms) = lookup' k ms Nothing
    where
      lookup' : MetaKey -> List Meta -> Maybe MetaValue -> Maybe MetaValue
      lookup' k []                      acc = acc
      lookup' k (m@(MkMeta k' v) :: ms) acc = if k == k'
                                                 then Just v
                                                 else lookup' k ms acc

namespace Data.Strings
  export
  capital : String -> String
  capital str
    = case strUncons str of
           Nothing => str
           Just (c, r) => strCons (toUpper c) r

  export
  camelize : String -> String
  camelize s = foldl (\acc, x => acc ++ capital x) "" (Data.List1.toList (split (== '-') s))

  export
  replaceAll : String -> String -> String -> String
  replaceAll old new str
    = replaceAll' (unpack old) (unpack new) (unpack str) []
    where
      replaceAll' : List Char -> List Char -> List Char -> List Char -> String
      replaceAll' old new []            acc = pack acc
      replaceAll' old new str@(x :: xs) acc = if isPrefixOf old str
                                                 then replaceAll' old new (drop (minus (length old) 1) xs) $ acc ++ new
                                                 else replaceAll' old new xs $ acc ++ [x]

namespace Data.List
  export
  index : Eq a => a -> List a -> Maybe Nat
  index a xs
    = index' a xs Z
    where
      index' : Eq elem => elem -> List elem -> Nat -> Maybe Nat
      index' a []        _ = Nothing
      index' a (x :: xs) i = if a == x
                                then Just i
                                else index' a xs (S i)

  export
  enumerate : List a -> List (Nat, a)
  enumerate xs
    = enumerate' xs Z []
    where
      enumerate' : List a -> Nat -> List (Nat, a) -> List (Nat, a)
      enumerate' [] _ acc = reverse acc
      enumerate' (x :: xs) idx acc = enumerate' xs (S idx) $ (idx, x) :: acc

  export
  join : String -> List String -> String
  join _   []        = ""
  join sep [x]       = x
  join sep (x :: xs) = foldl (\acc, y => acc ++ sep ++ y) x xs

  export
  flatten : List (List a) -> List a
  flatten = foldl (\acc, x => acc ++ x) []

namespace Data.Vect
  export
  join : String -> Vect n String -> String
  join _   []        = ""
  join sep [x]       = x
  join sep (x :: xs) = foldl (\acc, y => acc ++ sep ++ y) x xs

-----------
-- Event --
-----------

export
parametersOfEvents : List Event -> List Parameter
parametersOfEvents = (nubBy (\x, y => fst x == fst y)) . flatten . (map params)

----------
-- Tipe --
----------

export
constructTArrow : List Tipe -> Tipe -> Tipe
constructTArrow []        acc = acc
constructTArrow (x :: xs) acc = constructTArrow xs $ (TArrow x acc)

export
rootEnv : Fsm -> SortedMap Expression Tipe
rootEnv fsm
  = let eps = parametersOfEvents fsm.events
        env' = foldl (\acc, (n, t, _) => insert (IdentifyExpression ("@" ++ n)) t acc) Data.SortedMap.empty fsm.model
        env = foldl (\acc, (n, t, _) => insert (IdentifyExpression n) t acc) env' eps in
        env

----------------
-- Expression --
----------------

export
applicationExpressionFilter : Expression -> Bool
applicationExpressionFilter (ApplicationExpression _ _) = True
applicationExpressionFilter _                           = False

export
expressionsOfAction : Action -> List Expression
expressionsOfAction (AssignmentAction l r) = [l, r]
expressionsOfAction (OutputAction _ es)    = es

--------------------
-- TestExpression --
--------------------

export
expressionsOfTestExpression : TestExpression -> List Expression
expressionsOfTestExpression e
  = SortedSet.toList $ expressionsOfTestExpression' e SortedSet.empty
  where
    expressionsOfTestExpression' : TestExpression -> SortedSet Expression -> SortedSet Expression
    expressionsOfTestExpression' (PrimitiveTestExpression e)  acc = insert e acc
    expressionsOfTestExpression' (BinaryTestExpression _ l r) acc = expressionsOfTestExpression' l $ expressionsOfTestExpression' r acc
    expressionsOfTestExpression' (UnaryTestExpression _ t)    acc = expressionsOfTestExpression' t acc
    expressionsOfTestExpression' (CompareExpression  _ le re) acc = insert le $ insert re acc

-----------
-- State --
-----------

liftFromAndToStates : List Transition -> (SortedSet State, SortedSet State) -> (SortedSet State, SortedSet State)
liftFromAndToStates []                              acc          = acc
liftFromAndToStates ((MkTransition s d _) :: xs) (srcs, dsts) = liftFromAndToStates xs (insert s srcs, insert d dsts)

export
startState : Fsm -> Maybe State
startState fsm
  = let (fs, ds) = liftFromAndToStates (transitions fsm) (empty, empty) in
        case Data.SortedSet.toList (difference fs ds) of
             [] => Nothing
             (x :: xs) => Just x

export
stopState : Fsm -> SortedSet State
stopState fsm
  = let (fs, ds) = liftFromAndToStates (transitions fsm) (empty, empty) in
        difference ds fs

------------
-- Action --
------------

export
actionsOfTrigger : Trigger -> List Action
actionsOfTrigger (MkTrigger _ _ _ (Just as)) = as
actionsOfTrigger (MkTrigger _ _ _ Nothing)   = []

export
actionsOfTransition : Transition -> List (List Action)
actionsOfTransition t
  = nub $ filter (\x => length x > 0) $ map actionsOfTrigger t.triggers

export
actionsOfTransitions : List Transition -> List (List Action)
actionsOfTransitions ts
  = nub $ flatten $ map actionsOfTransition ts

export
actionsOfState : (State -> Maybe (List Action)) -> State -> List Action
actionsOfState f s
  = fromMaybe [] (f s)

export
actionsOfStates : (State -> Maybe (List Action)) -> List State -> List (List Action)
actionsOfStates f ss
  = nub $ filter (\x => length x > 0) $ map (actionsOfState f) ss

export
outputActionFilter : Action -> Bool
outputActionFilter (OutputAction _ _) = True
outputActionFilter _                  = False

export
outputActions : Fsm -> List Action
outputActions fsm
  = let as = flatten $ map ((filter outputActionFilter) . flatten) [ actionsOfTransitions fsm.transitions
                                                                   , actionsOfStates (\x => x.onEnter) fsm.states
                                                                   , actionsOfStates (\x => x.onExit) fsm.states
                                                                   ] in
        nubBy outputActionEq as
  where
    outputActionEq : Action -> Action -> Bool
    outputActionEq (OutputAction n1 _) (OutputAction n2 _) = n1 == n2
    outputActionEq _                   _                   = False

export
assignmentActionFilter : Action -> Bool
assignmentActionFilter (AssignmentAction _ _) = True
assignmentActionFilter _                      = False

export
assignmentActions : Fsm -> List Action
assignmentActions fsm
  = let as = flatten $ map ((filter assignmentActionFilter) . flatten ) [ actionsOfTransitions fsm.transitions
                                                                        , actionsOfStates (\x => x.onEnter) fsm.states
                                                                        , actionsOfStates (\x => x.onExit) fsm.states
                                                                        ] in
        nubBy assignmentActionEq as
  where
    assignmentActionEq : Action -> Action -> Bool
    assignmentActionEq (AssignmentAction l1 r1) (AssignmentAction l2 r2) = l1 == l2 && r1 == r2
    assignmentActionEq _                        _                        = False

----------------
-- Transition --
----------------

export
guardsOfTransition : Transition -> List TestExpression
guardsOfTransition t = Data.SortedSet.toList $ foldl (\acc, (MkTrigger _ _ x _) => case x of Nothing => acc; Just g => insert g acc) empty t.triggers
