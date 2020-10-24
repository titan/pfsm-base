module Pfsm

import Data.List
import Data.List1
import Data.SortedMap
import Data.SortedSet
import Data.Strings
import Data.Vect
import System
import System.File

import public Pfsm.Analyser
import Pfsm.Checker
import Pfsm.Data
import Pfsm.Parser

public export
data FsmIdStyle = FsmIdStyleGenerate
                | FsmIdStyleSession
                | FsmIdStyleUrl

export
Eq FsmIdStyle where
  (==) FsmIdStyleGenerate FsmIdStyleGenerate = True
  (==) FsmIdStyleSession  FsmIdStyleSession  = True
  (==) FsmIdStyleUrl      FsmIdStyleUrl      = True
  (==) _                  _                  = False

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

export
liftListIO : List (IO a) -> IO (List a)
liftListIO xs
  = do xs' <- foldl (\acc, x => do acc' <- acc; x' <- x; pure (x' :: acc')) (pure []) xs
       pure (reverse xs')

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

export
liftReferences : List Parameter -> List String
liftReferences params
  = nub $ foldl (\acc, (_, t, ms) =>
            case t of
                 TRecord n params' => acc ++ liftReferences params'
                 TList (TRecord n params') => acc ++ liftReferences params'
                 TDict _ (TRecord n params') => acc ++ liftReferences params'
                 _ => liftReference acc ms) [] params
  where
    liftReference : List String -> Maybe (List Meta) -> List String
    liftReference acc metas
      = case lookup "reference" metas of
             Just (MVString ref) => ref :: acc
             _ => acc

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
  enumerate
    = enumerate' [] Z
    where
      enumerate' : List (Nat, a) -> Nat -> List a -> List (Nat, a)
      enumerate' acc _   []        = reverse acc
      enumerate' acc idx (x :: xs) = enumerate' ((idx, x) :: acc) (S idx) xs

  export
  join : String -> List String -> String
  join _   []        = ""
  join sep [x]       = x
  join sep (x :: xs) = foldl (\acc, y => acc ++ sep ++ y) x xs

  export
  flatten : List (List a) -> List a
  flatten = foldl (\acc, x => acc ++ x) []

export
joinIO : String -> List (IO String) -> IO String
joinIO sep xs
 = do xs' <- liftListIO xs
      pure (List.join sep xs')

namespace Data.List1
  export
  enumerate : List1 a -> List1 (Nat, a)
  enumerate (x :: xs)
    = enumerate' ((Z, x) :: []) (S Z) xs
    where
      enumerate' : List1 (Nat, a) -> Nat -> List a -> List1 (Nat, a)
      enumerate' acc _   []        = reverse acc
      enumerate' acc idx (x :: xs) = enumerate' ((idx, x) :: (List1.toList acc)) (S idx) xs

  export
  join : String -> List1 String -> String
  join sep (x :: []) = x
  join sep (x :: xs) = foldl (\acc, y => acc ++ sep ++ y) x xs

  export
  length : List1 a -> Nat
  length (_ :: xs) = 1 + length xs

  export
  index : Eq a => a -> List1 a -> Maybe Nat
  index a (x :: xs)
    = if a == x
         then Just Z
         else do i <- index a xs
                 pure (i + 1)

  export
  elemBy : (a -> a -> Bool) -> a -> List1 a -> Bool
  elemBy p e (x :: xs) = p e x || elemBy p e xs

  public export
  filter : (p : a -> Bool) -> List1 a -> List a
  filter p (x :: xs)
     = if p x
          then x :: filter p xs
          else filter p xs

  public export
  (++) : (1 xs, ys : List1 a) -> List1 a
  (x :: []) ++ (y :: ys) = x :: (y :: ys)
  (x :: xs) ++ (y :: []) = x :: (xs ++ [y])
  (x :: xs) ++ (y :: ys) = x :: (xs ++ (y :: ys))

  public export
  flatten : List1 (List1 a) -> List1 a
  flatten (x :: []) = x
  flatten (x :: xs) = foldl (\acc, y => acc ++ y) x xs

namespace Data.Vect
  export
  join : String -> Vect n String -> String
  join _   []        = ""
  join sep [x]       = x
  join sep (x :: xs) = foldl (\acc, y => acc ++ sep ++ y) x xs

namespace Prelude.Types.Either
  export
  mapError : (a -> c) -> Either a b -> Either c b
  mapError f e = either (Left . f) (Right . id) e

-----------
-- Event --
-----------

export
fsmIdStyleOfEvent : Event -> FsmIdStyle
fsmIdStyleOfEvent (MkEvent _ _ metas)
  = case lookup "gateway.fsmid-style" metas of
         Just (MVString "generate") => FsmIdStyleGenerate
         Just (MVString "session") => FsmIdStyleSession
         Just (MVString "url") => FsmIdStyleUrl
         _ => FsmIdStyleUrl

export
parametersOfEvents : List1 Event -> List Parameter
parametersOfEvents = (nubBy (\x, y => fst x == fst y)) . flatten . (map params) . List1.toList

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

export
liftRecords : List Parameter -> List Tipe
liftRecords ps
  = liftRecords' ps []
  where
    liftRecordFromTipe : Tipe -> Maybe (Tipe, List Parameter)
    liftRecordFromTipe (TList t)        = liftRecordFromTipe t
    liftRecordFromTipe (TDict _ v)      = liftRecordFromTipe v
    liftRecordFromTipe t@(TRecord n ps) = Just (t, ps)
    liftRecordFromTipe _                = Nothing

    liftRecords' : List Parameter -> List Tipe -> List Tipe
    liftRecords' []                acc = acc
    liftRecords' ((_, t, _) :: xs) acc = case liftRecordFromTipe t of
                                              Nothing => liftRecords' xs acc
                                              Just (t, ps) => liftRecords' xs ((liftRecords ps) ++ (t :: acc))

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

export
applicationExpressionEqualityChecker : SortedMap Expression Tipe -> Expression -> Expression -> Bool
applicationExpressionEqualityChecker env a1@(ApplicationExpression n1 _) a2@(ApplicationExpression n2 _) = n1 == n2 && (inferType env a1) == (inferType env a2)
applicationExpressionEqualityChecker env _                               _                               = False

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
liftFromAndToStates []                           acc          = acc
liftFromAndToStates ((MkTransition s d _) :: xs) (srcs, dsts) = liftFromAndToStates xs (insert s srcs, insert d dsts)

export
startState : Fsm -> Maybe State
startState fsm
  = let (fs, ds) = liftFromAndToStates (List1.toList fsm.transitions) (empty, empty) in
        case Data.SortedSet.toList (difference fs ds) of
             [] => Nothing
             (x :: xs) => Just x

export
stopState : Fsm -> SortedSet State
stopState fsm
  = let (fs, ds) = liftFromAndToStates (List1.toList fsm.transitions) (empty, empty) in
        difference ds fs

------------
-- Action --
------------

export
actionsOfTransition : Transition -> List (List Action)
actionsOfTransition (MkTransition _ _ ts)
  = nub $ foldl (\acc, (MkTrigger _ _ _ as) => case as of Just as' => (List1.toList as') :: acc; Nothing => acc) [] ts

export
actionsOfTransitions : List1 Transition -> List (List Action)
actionsOfTransitions
  = nub . flatten . List1.toList . (map actionsOfTransition)

export
actionsOfState : (State -> Maybe (List Action)) -> State -> List Action
actionsOfState f
  = (fromMaybe []) . f

export
actionsOfStates : (State -> Maybe (List Action)) -> List1 State -> List (List Action)
actionsOfStates f
  = nub . (filter (\x => length x > 0)) . (List1.toList) . (map (actionsOfState f))

export
outputActionFilter : Action -> Bool
outputActionFilter (OutputAction _ _) = True
outputActionFilter _                  = False

export
outputActions : Fsm -> List Action
outputActions fsm
  = let as = List.flatten $ map ((filter outputActionFilter) . List.flatten) [ actionsOfTransitions $ fsm.transitions
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
  = let as = List.flatten $ map ((filter assignmentActionFilter) . List.flatten ) [ actionsOfTransitions $ fsm.transitions
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


---------
-- Fsm --
---------

export
loadFsm : String -> Either String Fsm
loadFsm src
  = do (sexp, _) <- mapError parseErrorToString $ parseSExp src
       (fsm, _) <- mapError parseErrorToString $ analyse sexp
       fsm' <- mapError checkersErrorToString $ check fsm defaultCheckingRules
       pure fsm'

export
loadFsmFromFile : String -> IO (Either String Fsm)
loadFsmFromFile file
  = do Right content <- readFile file
       | Left err => pure (Left $ show err)
       case loadFsm content of
            Left err => pure (Left err)
            Right fsm => pure (Right fsm)

export
fsmIdStyleOfFsm : Fsm -> FsmIdStyle
fsmIdStyleOfFsm (MkFsm _ _ _ _ _ _ metas)
  = case lookup "gateway.fsmid-style" metas of
         Just (MVString "session") => FsmIdStyleSession
         _ => FsmIdStyleUrl
