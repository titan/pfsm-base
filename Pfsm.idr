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

export
displayName : String -> Maybe (List Meta) -> String
displayName defaultValue metas
  = case lookup "display-name" metas of
         Just (MVString name) => name
         _ => defaultValue

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

export
joinIO : String -> List (IO String) -> IO String
joinIO sep xs
 = do xs' <- liftListIO xs
      pure (List.join sep xs')

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

----------
-- Tipe --
----------

export
liftRecords : List Parameter -> List Tipe
liftRecords ps
  = nub $ liftRecords' ps []
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

------------
-- Action --
------------

export
outputActionEqualityChecker : Action -> Action -> Bool
outputActionEqualityChecker (OutputAction n1 _) (OutputAction n2 _) = n1 == n2
outputActionEqualityChecker _                   _                   = False

export
assignmentActionEqualityChecker : Action -> Action -> Bool
assignmentActionEqualityChecker (AssignmentAction l1 r1) (AssignmentAction l2 r2) = l1 == l2 && r1 == r2
assignmentActionEqualityChecker _                        _                        = False

-----------
-- State --
-----------

export
liftActionsFromState : State -> List Action
liftActionsFromState (MkState _ (Just enas) (Just exas) _) = enas ++ exas
liftActionsFromState (MkState _ (Just enas) Nothing     _) = enas
liftActionsFromState (MkState _ Nothing     (Just exas) _) = exas
liftActionsFromState (MkState _ Nothing     Nothing     _) = []

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
