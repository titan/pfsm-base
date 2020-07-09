module Pfsm.Data

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

export
primTypeStrs : List String
primTypeStrs = ["byte", "char", "short", "ushort", "int", "uint", "long", "ulong", "real", "string"]

namespace PrimType
  export
  fromString : String -> Maybe PrimType
  fromString str
    = case str of
        "byte" => Just PTByte
        "char" => Just PTChar
        "short" => Just PTShort
        "ushort" => Just PTUShort
        "int" => Just PTInt
        "uint" => Just PTUInt
        "long" => Just PTLong
        "ulong" => Just PTULong
        "real" => Just PTReal
        "string" => Just PTString
        _ => Nothing

public export
data Tipe = TPrimType PrimType
          | TList Tipe
          | TDict PrimType Tipe

public export
data Expression = ApplicationExpression String (List Expression)
                | BooleanExpression Bool
                | IdentifyExpression String
                | IntegerLiteralExpression Integer
                | RealLiteralExpression Double
                | StringLiteralExpression String

export
toBool : String -> Bool
toBool "true" = True
toBool _ = False

public export
data BinaryBoolOperation = AndBoolOperation
                         | OrBoolOperation

namespace BinaryBoolOperation
  export
  fromString : String -> Maybe BinaryBoolOperation
  fromString "and" = Just AndBoolOperation
  fromString "or"  = Just OrBoolOperation
  fromString _     = Nothing

public export
data UnaryBoolOperation = NotBoolOperation

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

public export
data Action = ActionAssignment Expression Expression
            | ActionReturn Expression

public export
Name : Type
Name = String

public export
Description : Type
Description = String

public export
StateRef : Type
StateRef = String

public export
EventRef : Type
EventRef = String

public export
RoleRef : Type
RoleRef = String

public export
MetaKey: Type
MetaKey = String

public export
record Meta where
  constructor MkMeta
  key: MetaKey
  value: Either String Meta

public export
record Role where
  constructor MkRole
  name: Name
  description: Description

public export
record State where
  constructor MkState
  name: Name
  description: Description
  onEnter: Maybe (List Action)
  onExit: Maybe (List Action)
  metas: Maybe (List Meta)

public export
record Event where
  constructor MkEvent
  name: Name
  params: List (Name, Tipe, Description)

public export
record Transition where
  constructor MkTransition
  src: StateRef
  dst: StateRef
  triggerBy: RoleRef
  event: EventRef
  guard: Maybe BoolExpression
  actions: Maybe(List Action)

public export
record Fsm where
  constructor MkFsm
  name: Name
  description: Description
  model: List (Name, Tipe, Description)
  roles: List Role
  events: List Event
  states: List State
  transitions: List Transition
  metas: Maybe (List Meta)
