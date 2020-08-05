module Pfsm.Data

import Data.List

public export
Name : Type
Name = String

public export
data PrimType = PTByte
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
primTypeStrs = ["byte", "char", "short", "ushort", "int", "uint", "long", "ulong", "real", "string"]

namespace PrimType
  export
  fromString : String -> Maybe PrimType
  fromString str
    = case str of
        "byte"   => Just PTByte
        "char"   => Just PTChar
        "short"  => Just PTShort
        "ushort" => Just PTUShort
        "int"    => Just PTInt
        "uint"   => Just PTUInt
        "long"   => Just PTLong
        "ulong"  => Just PTULong
        "real"   => Just PTReal
        "string" => Just PTString
        _        => Nothing

public export
data Tipe = TPrimType PrimType
          | TList Tipe
          | TDict PrimType Tipe

export
Show Tipe where
  show (TPrimType pt) = show pt
  show (TList t)      = "(list " ++ (show t) ++ ")"
  show (TDict k v)    = "(dict " ++ (show k) ++ " " ++ (show v) ++ ")"

export
Eq Tipe where
  (==) (TPrimType p1) (TPrimType p2) = p1 == p2
  (==) (TList t1)     (TList t2)     = t1 == t2
  (==) (TDict k1 v1)  (TDict k2 v2)  = k1 == k2 && v1 == v2
  (==) _              _              = False

export
Ord Tipe where
  compare t1 t2 = compare (show t1) (show t2)


public export
data Expression = ApplicationExpression String (List Expression)
                | BooleanExpression Bool
                | IdentifyExpression String
                | IntegerLiteralExpression Int
                | RealLiteralExpression Double
                | StringLiteralExpression String

export
Show Expression where
  show (ApplicationExpression n es) = "(" ++ n ++ (foldl (\a, x => a ++ " " ++ show(x)) "" es) ++ ")"
  show (BooleanExpression b)        = show b
  show (IdentifyExpression s)       = s
  show (IntegerLiteralExpression i) = show i
  show (RealLiteralExpression r)    = show r
  show (StringLiteralExpression s)  = s

export
Eq Expression where
  (==) (ApplicationExpression s1 es1) (ApplicationExpression s2 es2) = s1 == s2 && es1 == es2
  (==) (BooleanExpression b1)         (BooleanExpression b2)         = b1 == b2
  (==) (IdentifyExpression i1)        (IdentifyExpression i2)        = i1 == i2
  (==) (IntegerLiteralExpression i1)  (IntegerLiteralExpression i2)  = i1 == i2
  (==) (RealLiteralExpression r1)     (RealLiteralExpression r2)     = r1 == r2
  (==) (StringLiteralExpression s1)   (StringLiteralExpression s2)   = s1 == s2
  (==) _                              _                              = False

export
Ord Expression where
  compare e1 e2 = compare (show e1) (show e2)

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
data CompareOperation = EqualsToOperation
                      | LessThanOperation
                      | LessThanOrEqualsToOperation
                      | GreatThanOperation
                      | GreatThanOrEqualsToOperation

Show CompareOperation where
  show EqualsToOperation            = "="
  show LessThanOperation            = "<"
  show LessThanOrEqualsToOperation  = "<="
  show GreatThanOperation           = ">"
  show GreatThanOrEqualsToOperation = ">="

Eq CompareOperation where
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
  fromString "<"  = Just LessThanOperation
  fromString "<=" = Just LessThanOrEqualsToOperation
  fromString ">"  = Just GreatThanOperation
  fromString ">=" = Just GreatThanOrEqualsToOperation
  fromString _    = Nothing

public export
data BoolExpression = PrimitiveBoolExpression Expression
                    | BinaryBoolExpression BinaryBoolOperation BoolExpression BoolExpression
                    | UnaryBoolExpression UnaryBoolOperation BoolExpression
                    | CompareExpression CompareOperation Expression Expression

export
Show BoolExpression where
  show (PrimitiveBoolExpression e)     = show e
  show (BinaryBoolExpression op e1 e2) = "(" ++ (show op) ++ " " ++ (show e1) ++ " " ++ (show e2) ++ ")"
  show (UnaryBoolExpression op e)      = "(" ++ (show op) ++ " " ++ (show e) ++ ")"
  show (CompareExpression op e1 e2)    = "(" ++ (show op) ++ " " ++ (show e1) ++ " " ++ (show e2) ++ ")"

export
Eq BoolExpression where
  (==) (PrimitiveBoolExpression e1)       (PrimitiveBoolExpression e2)       = e1 == e2
  (==) (BinaryBoolExpression op1 ea1 eb1) (BinaryBoolExpression op2 ea2 eb2) = (op1 == op2) && ((ea1 == ea2) || (ea1 == eb2) || (eb1 == eb2) || (eb1 == ea2))
  (==) (UnaryBoolExpression op1 e1)       (UnaryBoolExpression op2 e2)       = (op1 == op2) && (e1 == e2)
  (==) (CompareExpression op1 ea1 eb1)    (CompareExpression op2 ea2 eb2)    = (op1 == op2) && (ea1 == ea2) && (eb1 == eb2)
  (==) _                                  _                                  = False

public export
data Action = ActionAssignment Expression Expression
            | ActionOutput Name (List Expression)

export
Show Action where
  show (ActionAssignment e1 e2) = "(set! " ++ (show e1) ++ " " ++ (show e2) ++ ")"
  show (ActionOutput n [])      = "(return " ++ n ++ ")"
  show (ActionOutput n es)      = "(return " ++ n ++ (foldl (\acc, x => acc ++ " " ++ (show x)) "" es) ++ ")"

export
Eq Action where
  (==) (ActionAssignment x1 x2) (ActionAssignment y1 y2) = x1 == y1 && y2 == y2 
  (==) (ActionOutput n1 es1)    (ActionOutput n2 es2)    = n1 == n2 && es1 == es2
  (==) _                        _                        = False

export
Ord Action where
  compare a1 a2 = compare (show a1) (show a2)

public export
StateRef : Type
StateRef = String

public export
EventRef : Type
EventRef = String

public export
ParticipantRef : Type
ParticipantRef = String

public export
MetaKey: Type
MetaKey = String

public export
record Meta where
  constructor MkMeta
  key: MetaKey
  value: Either String Meta

export
Eq Meta where
  (==) m1 m2 = (key m1) == (key m2) && (value m1) == (value m2)

export
Show Meta where
  show (MkMeta k (Left s))  = "(meta \"" ++ k ++ "\" \"" ++ s ++ "\")"
  show (MkMeta k (Right m)) = "(meta \"" ++ k ++ "\" " ++ show (m) ++ ")"

public export
record Participant where
  constructor MkParticipant
  name: Name
  metas: List Meta

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
  (==) (MkState n1 ens1 exs1 ms1) (MkState n2 ens2 exs2 ms2) = n1 == n2 && ens1 == ens2 && exs1 == exs2 && ms1 == ms2

export
Ord State where
  compare (MkState n1 _ _ _) (MkState n2 _ _ _) = compare n1 n2

public export
record Event where
  constructor MkEvent
  name: Name
  params: List (Name, Tipe, Maybe (List Meta))

export
Show Event where
  show (MkEvent n ps) = "(event " ++ n ++ " " ++ (foldl (\a, (pn, pt, pms) => a ++ "(the " ++ (show pt) ++ " " ++ pn ++ " " ++ (show pms) ++ ")") "" ps) ++ ")"

export
Eq Event where
   (==) e1 e2 = (name e1) == (name e2) && parameq (params e1) (params e2)
              where
                parameq : List (Name, Tipe, Maybe (List Meta)) -> List (Name, Tipe, Maybe (List Meta)) -> Bool
                parameq []                  ys                  = False
                parameq xs                  []                  = False
                parameq ((xn, xt, _) :: xs) ((yn, yt, _) :: ys) = xn == yn && xt == yt && parameq xs ys

export
Ord Event where
  compare (MkEvent n1 ps1) (MkEvent n2 ps2) = compare (n1 ++ (show ps1)) (n2 ++ (show ps2))

public export
record Transition where
  constructor MkTransition
  src: StateRef
  dst: StateRef
  triggerBy: ParticipantRef
  event: EventRef
  guard: Maybe BoolExpression
  actions: Maybe (List Action)

export
Show Transition where
  show (MkTransition src dst triggerBy event (Just guard) actions) = "(transition (from-to " ++ src ++ " " ++ dst ++ ") (trigger-by " ++ triggerBy ++ " " ++ event ++ " (where " ++ (show guard) ++ ")) (action " ++ (show actions) ++ "))"
  show (MkTransition src dst triggerBy event Nothing      actions) = "(transition (from-to " ++ src ++ " " ++ dst ++ ") (trigger-by " ++ triggerBy ++ " " ++ event ++ ") (action " ++ (show actions) ++ "))"

export
Eq Transition where
  (==) t1 t2 = (t1.src == t2.src) && (t1.dst == t2.dst) && (t1.triggerBy == t2.triggerBy) && (t1.event == t2.event) && (t1.guard == t2.guard) && (t1.actions == t2.actions)

export
Ord Transition where
  compare t1 t2 = compare (show t1) (show t2)


public export
record Fsm where
  constructor MkFsm
  name: Name
  model: List (Name, Tipe, Maybe (List Meta))
  participants: List Participant
  events: List Event
  states: List State
  transitions: List Transition
  metas: Maybe (List Meta)
