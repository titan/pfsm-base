module Pfsm.Data

import Data.List
import Data.List1
import Data.Maybe
import Data.SortedMap

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

public export
Name : Type
Name = String

public export
data PrimType = PTBool
              | PTByte
              | PTChar
              | PTShort
              | PTUShort
              | PTInt
              | PTUInt
              | PTLong
              | PTULong
              | PTReal
              | PTString

Show PrimType where
  show PTBool   = "bool"
  show PTByte   = "byte"
  show PTChar   = "char"
  show PTShort  = "short"
  show PTUShort = "ushort"
  show PTInt    = "int"
  show PTUInt   = "uint"
  show PTLong   = "long"
  show PTULong  = "ulong"
  show PTReal   = "real"
  show PTString = "string"

export
Eq PrimType where
  (==) PTBool   PTBool   = True
  (==) PTByte   PTByte   = True
  (==) PTChar   PTChar   = True
  (==) PTShort  PTShort  = True
  (==) PTUShort PTUShort = True
  (==) PTInt    PTInt    = True
  (==) PTUInt   PTUInt   = True
  (==) PTLong   PTLong   = True
  (==) PTULong  PTULong  = True
  (==) PTReal   PTReal   = True
  (==) PTString PTString = True
  (==) _        _        = False

export
primTypeStrs : List String
primTypeStrs = ["bool", "byte", "char", "short", "ushort", "int", "uint", "long", "ulong", "real", "string"]

namespace PrimType
  export
  fromString : String -> Maybe PrimType
  fromString "bool"   = Just PTBool
  fromString "byte"   = Just PTByte
  fromString "char"   = Just PTChar
  fromString "short"  = Just PTShort
  fromString "ushort" = Just PTUShort
  fromString "int"    = Just PTInt
  fromString "uint"   = Just PTUInt
  fromString "long"   = Just PTLong
  fromString "ulong"  = Just PTULong
  fromString "real"   = Just PTReal
  fromString "string" = Just PTString
  fromString _        = Nothing

public export
MetaKey: Type
MetaKey = String

public export
data MetaValue = MVString String
               | MVList (List String)
               | MVDict (SortedMap String String)

export
Show MetaValue where
  show (MVString s) = show s
  show (MVList vs)  = "(list " ++ (foldl (\acc, x => acc ++ " " ++ (show x)) "" vs) ++ ")"
  show (MVDict vs)  = "(dict " ++ (foldl (\acc, (x, y) => acc ++ " (" ++ (show x) ++ " " ++ (show y) ++ ")") "" (SortedMap.toList vs)) ++ ")"

export
Eq MetaValue where
  (==) v1 v2 = (show v1) == (show v2)

export
Ord MetaValue where
  compare v1 v2 = compare (show v1) (show v2)

public export
record Meta where
  constructor MkMeta
  key: MetaKey
  value: MetaValue

export
Show Meta where
  show (MkMeta k v)  = "(meta " ++ (show k) ++ " " ++ (show v) ++ ")"

export
Eq Meta where
  (==) m1 m2 = (key m1) == (key m2) && (value m1) == (value m2)

export
Ord Meta where
  compare m1 m2 = compare (show m1) (show m2)

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

mutual
  public export
  data Tipe = TPrimType PrimType
            | TList Tipe
            | TDict PrimType Tipe
            | TArrow Tipe Tipe
            | TRecord Name (List Parameter)
            | TUnit

  public export
  Parameter : Type
  Parameter = (Name, Tipe, Maybe (List Meta))

export
Show Tipe where
  show (TPrimType pt) = show pt
  show (TList t)      = "(list " ++ (show t) ++ ")"
  show (TDict k v)    = "(dict " ++ (show k) ++ " " ++ (show v) ++ ")"
  show (TArrow p r)   = "(-> " ++ (show p) ++ " " ++ (show r) ++ ")"
  show (TRecord n ts) = "(record " ++ (show n) ++ (foldl (\acc, x => acc ++ " " ++ (show x)) "" ts) ++ ")"
  show TUnit          = "()"

export
Eq Tipe where
  (==) (TPrimType p1)   (TPrimType p2)   = p1 == p2
  (==) (TList t1)       (TList t2)       = t1 == t2
  (==) (TDict k1 v1)    (TDict k2 v2)    = k1 == k2 && v1 == v2
  (==) (TArrow p1 r1)   (TArrow p2 r2)   = p1 == p2 && r1 == r2
  (==) (TRecord n1 ts1) (TRecord n2 ts2) = n1 == n2 && ts1 == ts2
  (==) TUnit            TUnit            = True
  (==) _                _                = False

export
Ord Tipe where
  compare t1 t2 = compare (show t1) (show t2)

export
constructTArrow : List Tipe -> Tipe -> Tipe
constructTArrow []        acc = acc
constructTArrow (x :: xs) acc = constructTArrow xs $ (TArrow x acc)

public export
data Expression = ApplicationExpression String (List Expression)
                | BooleanExpression Bool
                | IdentifyExpression String
                | IntegerLiteralExpression Int
                | RealLiteralExpression Double
                | CharLiteralExpression Char
                | StringLiteralExpression String

export
Show Expression where
  show (ApplicationExpression n es) = "(" ++ n ++ (foldl (\a, x => a ++ " " ++ show(x)) "" es) ++ ")"
  show (BooleanExpression b)        = show b
  show (IdentifyExpression s)       = s
  show (IntegerLiteralExpression i) = show i
  show (RealLiteralExpression r)    = show r
  show (CharLiteralExpression c)    = show c
  show (StringLiteralExpression s)  = s

export
Eq Expression where
  (==) (ApplicationExpression s1 es1) (ApplicationExpression s2 es2) = s1 == s2 && es1 == es2
  (==) (BooleanExpression b1)         (BooleanExpression b2)         = b1 == b2
  (==) (IdentifyExpression i1)        (IdentifyExpression i2)        = i1 == i2
  (==) (IntegerLiteralExpression i1)  (IntegerLiteralExpression i2)  = i1 == i2
  (==) (RealLiteralExpression r1)     (RealLiteralExpression r2)     = r1 == r2
  (==) (CharLiteralExpression c1)     (CharLiteralExpression c2)     = c1 == c2
  (==) (StringLiteralExpression s1)   (StringLiteralExpression s2)   = s1 == s2
  (==) _                              _                              = False

export
Ord Expression where
  compare e1 e2 = compare (show e1) (show e2)

export
inferType : SortedMap Expression Tipe -> Expression -> Maybe Tipe
inferType env (ApplicationExpression _ es) = Just $ foldl (\acc, x => TArrow x acc ) TUnit (map ((fromMaybe TUnit) . (inferType env)) es)
inferType env (BooleanExpression _)        = Just (TPrimType PTBool)
inferType env i@(IdentifyExpression _)     = lookup i env
inferType env (IntegerLiteralExpression _) = Just (TPrimType PTInt)
inferType env (RealLiteralExpression _)    = Just (TPrimType PTReal)
inferType env (CharLiteralExpression _)    = Just (TPrimType PTChar)
inferType env (StringLiteralExpression _)  = Just (TPrimType PTString)
inferType _   _                            = Nothing

liftArrowParams : Tipe -> List Tipe -> List Tipe
liftArrowParams (TArrow a b@(TArrow _ _)) acc = liftArrowParams b (a :: acc)
liftArrowParams (TArrow a b)              acc = b :: (a :: acc)
liftArrowParams _                         acc = acc

export
fixTypeOfApplicationExpression : SortedMap Expression Tipe -> Maybe Tipe -> Maybe Tipe -> Maybe Tipe
fixTypeOfApplicationExpression env (Just ats@(TArrow a b)) (Just rt) = case liftArrowParams ats [] of
                                                                            []        => Just (TArrow TUnit rt)
                                                                            (x :: xs) => Just (constructTArrow (reverse xs) rt)
fixTypeOfApplicationExpression env _                       (Just rt) = Just (TArrow TUnit rt)
fixTypeOfApplicationExpression env _                       _         = Nothing

export
toBool : String -> Bool
toBool "true" = True
toBool _ = False

public export
data BinaryBoolOperation = AndBoolOperation
                         | OrBoolOperation

export
Show BinaryBoolOperation where
  show AndBoolOperation = "and"
  show OrBoolOperation  = "or"

export
Eq BinaryBoolOperation where
  (==) AndBoolOperation AndBoolOperation = True
  (==) OrBoolOperation  OrBoolOperation  = True
  (==) _                _                = False

namespace BinaryBoolOperation
  export
  fromString : String -> Maybe BinaryBoolOperation
  fromString "and" = Just AndBoolOperation
  fromString "or"  = Just OrBoolOperation
  fromString _     = Nothing

public export
data UnaryBoolOperation = NotBoolOperation

export
Show UnaryBoolOperation where
  show NotBoolOperation = "not"

export
Eq UnaryBoolOperation where
  (==) NotBoolOperation NotBoolOperation = True
  (==) _                _                = False

namespace UnaryBoolOperation
  export
  fromString : String -> Maybe UnaryBoolOperation
  fromString "not" = Just NotBoolOperation
  fromString _     = Nothing

public export
data CompareOperation = NotEqualsToOperation
                      | EqualsToOperation
                      | LessThanOperation
                      | LessThanOrEqualsToOperation
                      | GreatThanOperation
                      | GreatThanOrEqualsToOperation

export
Show CompareOperation where
  show NotEqualsToOperation         = "<>"
  show EqualsToOperation            = "="
  show LessThanOperation            = "<"
  show LessThanOrEqualsToOperation  = "<="
  show GreatThanOperation           = ">"
  show GreatThanOrEqualsToOperation = ">="

export
Eq CompareOperation where
  (==) NotEqualsToOperation         NotEqualsToOperation         = True
  (==) EqualsToOperation            EqualsToOperation            = True
  (==) LessThanOperation            LessThanOperation            = True
  (==) LessThanOrEqualsToOperation  LessThanOrEqualsToOperation  = True
  (==) GreatThanOperation           GreatThanOperation           = True
  (==) GreatThanOrEqualsToOperation GreatThanOrEqualsToOperation = True
  (==) _                            _                            = False

namespace CompareOperation
  export
  fromString : String -> Maybe CompareOperation
  fromString "="  = Just EqualsToOperation
  fromString "==" = Just EqualsToOperation
  fromString "<>" = Just NotEqualsToOperation
  fromString "<"  = Just LessThanOperation
  fromString "<=" = Just LessThanOrEqualsToOperation
  fromString ">"  = Just GreatThanOperation
  fromString ">=" = Just GreatThanOrEqualsToOperation
  fromString _    = Nothing

public export
data TestExpression = PrimitiveTestExpression Expression
                    | BinaryTestExpression BinaryBoolOperation TestExpression TestExpression
                    | UnaryTestExpression UnaryBoolOperation TestExpression
                    | CompareExpression CompareOperation Expression Expression

export
Show TestExpression where
  show (PrimitiveTestExpression e)     = show e
  show (BinaryTestExpression op e1 e2) = "(" ++ (show op) ++ " " ++ (show e1) ++ " " ++ (show e2) ++ ")"
  show (UnaryTestExpression op e)      = "(" ++ (show op) ++ " " ++ (show e) ++ ")"
  show (CompareExpression op e1 e2)    = "(" ++ (show op) ++ " " ++ (show e1) ++ " " ++ (show e2) ++ ")"

export
Eq TestExpression where
  (==) (PrimitiveTestExpression e1)       (PrimitiveTestExpression e2)       = e1 == e2
  (==) (BinaryTestExpression op1 ea1 eb1) (BinaryTestExpression op2 ea2 eb2) = (op1 == op2) && ((ea1 == ea2) || (ea1 == eb2) || (eb1 == eb2) || (eb1 == ea2))
  (==) (UnaryTestExpression op1 e1)       (UnaryTestExpression op2 e2)       = (op1 == op2) && (e1 == e2)
  (==) (CompareExpression op1 ea1 eb1)    (CompareExpression op2 ea2 eb2)    = (op1 == op2) && (ea1 == ea2) && (eb1 == eb2)
  (==) _                                  _                                  = False

export
Ord TestExpression where
  compare b1 b2 = compare (show b1) (show b2)

public export
record Port where
  constructor MkPort
  name: Name
  tipe: Tipe

export
Show Port where
  show (MkPort n t) = "(port " ++ n ++ " " ++ (show t) ++ ")"

export
Eq Port where
  (==) (MkPort n1 t1) (MkPort n2 t2) = (n1 == n2) && (t1 == t2)

public export
data Action = AssignmentAction Expression Expression
            | OutputAction Port (List Expression)

export
Show Action where
  show (AssignmentAction e1 e2)       = "(set! " ++ (show e1) ++ " " ++ (show e2) ++ ")"
  show (OutputAction (MkPort n _) []) = "(output" ++ n ++ ")"
  show (OutputAction (MkPort n _) es) = "(output " ++ n ++ (foldl (\acc, x => acc ++ " " ++ (show x)) "" es) ++ ")"

export
Eq Action where
  (==) a1 a2 = (show a1) == (show a2)

export
Ord Action where
  compare (OutputAction (MkPort n1 _) _) (OutputAction (MkPort n2 _) _) = compare n1 n2
  compare a1                             a2                             = compare (show a1) (show a2)

public export
record Participant where
  constructor MkParticipant
  name: Name
  metas: Maybe (List Meta)

export
Show Participant where
  show (MkParticipant n ms) = "(participant " ++ n ++ " " ++ (show ms) ++ ")"

export
Eq Participant where
  (==) (MkParticipant n1 _) (MkParticipant n2 _) = n1 == n2

public export
record State where
  constructor MkState
  name: Name
  onEnter: Maybe (List Action)
  onExit: Maybe (List Action)
  metas: Maybe (List Meta)

export
Show State where
  show (MkState n (Just ens) (Just exs) (Just ms)) = "(state " ++ n ++ " (on-enter " ++ (foldl (\a, x => a ++ (show x)) "" ens) ++ ")" ++ " (on-exit " ++ (foldl (\a, x => a ++ (show x)) "" exs) ++ ") " ++ (foldl (\a, x => a ++ (show x)) "" ms) ++ ")"
  show (MkState n Nothing (Just exs) (Just ms))    = "(state " ++ n ++ " (on-exit " ++ (foldl (\a, x => a ++ (show x)) "" exs) ++ ") " ++ (foldl (\a, x => a ++ (show x)) "" ms) ++ ")"
  show (MkState n (Just ens) Nothing (Just ms))    = "(state " ++ n ++ " (on-enter " ++ (foldl (\a, x => a ++ (show x)) "" ens) ++ ") " ++ (foldl (\a, x => a ++ (show x)) "" ms) ++ ")"
  show (MkState n (Just ens) (Just exs) Nothing)   = "(state " ++ n ++ " (on-enter " ++ (foldl (\a, x => a ++ (show x)) "" ens) ++ ") " ++ "(on-exit " ++ (foldl (\a, x => a ++ (show x)) "" exs) ++ ") " ++  ")"
  show (MkState n (Just ens) Nothing Nothing)      = "(state " ++ n ++ " (on-enter " ++ (foldl (\a, x => a ++ (show x)) "" ens) ++ "))"
  show (MkState n Nothing (Just exs) Nothing)      = "(state " ++ n ++ " (on-exit " ++ (foldl (\a, x => a ++ (show x)) "" exs) ++ "))"
  show (MkState n Nothing Nothing (Just ms))       = "(state " ++ n ++ " " ++ (foldl (\a, x => a ++ (show x)) "" ms) ++ ")"
  show (MkState n Nothing Nothing Nothing)         = "(state " ++ n ++ ")"

export
Eq State where
  (==) s1 s2 = (show s1) == (show s2)

export
Ord State where
  compare (MkState n1 _ _ _) (MkState n2 _ _ _) = compare n1 n2

public export
record Event where
  constructor MkEvent
  name: Name
  params: List Parameter
  metas: Maybe (List Meta)

export
Show Event where
  show (MkEvent n ps ms) = "(event " ++ n ++ (foldl (\acc, (pn, pt, pms) => acc ++ " (the " ++ (show pt) ++ " " ++ pn ++ " " ++ (show pms) ++ ")") "" ps) ++ " " ++ (show ms) ++ ")"

export
Eq Event where
  (==) e1 e2 = (show e1) == (show e2)

export
Ord Event where
  compare e1 e2 = compare (show e1) (show e2)

export
parametersOfEvents : List1 Event -> List Parameter
parametersOfEvents = (nubBy (\x, y => fst x == fst y)) . flatten . (map params) . List1.toList

public export
record Trigger where
  constructor MkTrigger
  participants: List1 Participant
  event: Event
  guard: Maybe TestExpression
  actions: Maybe (List1 Action)

export
Show Trigger where
  show (MkTrigger ps e (Just g) (Just as)) = "(trigger " ++ (show ps) ++ " " ++ (show e) ++ " (where " ++ (show g) ++ ") (action" ++ (foldl (\acc, x => acc ++ " " ++ (show x)) "" as) ++ "))"
  show (MkTrigger ps e Nothing  (Just as)) = "(trigger " ++ (show ps) ++ " " ++ (show e) ++ " (action" ++ (foldl (\acc, x => acc ++ " " ++ (show x)) "" as) ++ "))"
  show (MkTrigger ps e (Just g) Nothing)   = "(trigger " ++ (show ps) ++ " " ++ (show e) ++ " (where " ++ (show g) ++ "))"
  show (MkTrigger ps e Nothing  Nothing)   = "(trigger " ++ (show ps) ++ " " ++ (show e) ++ ")"

export
Eq Trigger where
  (==) t1 t2 = (show t1) == (show t2)

export
Ord Trigger where
  compare t1 t2 = compare (show t1) (show t2)

public export
record Transition where
  constructor MkTransition
  src: State
  dst: State
  triggers: List1 Trigger

export
Show Transition where
  show (MkTransition src dst triggers) = "(transition (from-to " ++ (show src) ++ " " ++ (show dst) ++ ")" ++ (foldl (\acc,x => acc ++ " " ++ (show x)) "" triggers) ++ ")"

export
Eq Transition where
  (==) t1 t2 = (show t1) == (show t2)

export
Ord Transition where
  compare t1 t2 = compare (show t1) (show t2)

export
actionsOfTransition : Transition -> List (List Action)
actionsOfTransition (MkTransition _ _ ts)
  = foldl (\acc, (MkTrigger _ _ _ as) => case as of Just as' => (List1.toList as') :: acc; Nothing => acc) [] ts

export
actionsOfTransitions : List1 Transition -> List (List Action)
actionsOfTransitions
  = flatten . List1.toList . (map actionsOfTransition)

export
actionsOfState : (State -> Maybe (List Action)) -> State -> List Action
actionsOfState f
  = (fromMaybe []) . f

export
actionsOfStates : (State -> Maybe (List Action)) -> List1 State -> List (List Action)
actionsOfStates f
  = (filter (\x => length x > 0)) . (List1.toList) . (map (actionsOfState f))

public export
record Fsm where
  constructor MkFsm
  name: Name
  model: List Parameter
  ports: List Port
  participants: List1 Participant
  events: List1 Event
  states: List1 State
  transitions: List1 Transition
  metas: Maybe (List Meta)

export
outputActionFilter : Action -> Bool
outputActionFilter (OutputAction _ _) = True
outputActionFilter _                  = False

export
liftOutputActions : List1 State -> List1 Transition -> List Action
liftOutputActions states transitions
  = let as = List.flatten $ map ((filter outputActionFilter) . List.flatten) [ actionsOfTransitions $ transitions
                                                                             , actionsOfStates (\x => x.onEnter) states
                                                                             , actionsOfStates (\x => x.onExit) states
                                                                             ] in
        as

export
assignmentActionFilter : Action -> Bool
assignmentActionFilter (AssignmentAction _ _) = True
assignmentActionFilter _                      = False

export
liftAssignmentActions : List1 State -> List1 Transition -> List Action
liftAssignmentActions states transitions
  = let as = List.flatten $ map ((filter assignmentActionFilter) . List.flatten ) [ actionsOfTransitions $ transitions
                                                                                  , actionsOfStates (\x => x.onEnter) states
                                                                                  , actionsOfStates (\x => x.onExit) states
                                                                                  ] in
        as

export
rootEnv : Fsm -> SortedMap Expression Tipe
rootEnv fsm
  = let eps = parametersOfEvents fsm.events
        env' = foldl (\acc, (n, t, _) => insert (IdentifyExpression ("@" ++ n)) t acc) Data.SortedMap.empty fsm.model
        env = foldl (\acc, (n, t, _) => insert (IdentifyExpression n) t acc) env' eps in
        env
