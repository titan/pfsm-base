module Pfsm.Analyser

import Control.Delayed
import Data.Either
import Data.List
import Data.List1
import Data.Maybe
import Data.SortedMap
import Text.Parser.Core
import Text.Parser
import Pfsm.Data
import Pfsm.Parser

StateRef : Type
StateRef = String

EventRef : Type
EventRef = String

ParticipantRef : Type
ParticipantRef = String

data ActionShadow = AssignmentActionShadow Expression Expression
                  | OutputActionShadow Name (List Expression)

record TriggerShadow where
  constructor MkTriggerShadow
  participants: List ParticipantRef
  event: EventRef
  guard: Maybe TestExpression
  actions: Maybe (List ActionShadow)

record TransitionShadow where
  constructor MkTransitionShadow
  src: StateRef
  dst: StateRef
  triggers: List TriggerShadow

mutual
  data TipeShadow = TPrimTypeShadow PrimType
                  | TListShadow (Either String TipeShadow)
                  | TDictShadow PrimType (Either String TipeShadow)
                  | TArrowShadow TipeShadow TipeShadow
                  | TRecordShadow Name (List ParameterShadow)
                  | TUnitShadow

  ParameterShadow : Type
  ParameterShadow = (Name, Either String TipeShadow, Maybe (List Meta))

record EventShadow where
  constructor MkEventShadow
  name: Name
  params: List ParameterShadow
  metas: Maybe (List Meta)

record PortShadow where
  constructor MkPortShadow
  name: Name
  tipe: List TipeShadow

record StateShadow where
  constructor MkStateShadow
  name: Name
  onEnter: Maybe (List ActionShadow)
  onExit: Maybe (List ActionShadow)
  metas: Maybe (List Meta)

------------
-- Helper --
------------

bold : String -> String
bold str = "\ESC[1m" ++ str ++ "\ESC[0m"

toMaybe : List a -> Maybe (List a)
toMaybe [] = Nothing
toMaybe xs = Just xs

derefParticipant : ParticipantRef -> List Participant -> Maybe Participant
derefParticipant _   []        = Nothing
derefParticipant ref (x :: xs) = if name x == ref
                              then Just x
                              else derefParticipant ref xs

derefParticipants : List ParticipantRef -> List Participant -> List (Maybe Participant)
derefParticipants prs ps
  = derefParticipants' prs ps []
  where
    derefParticipants' : List ParticipantRef -> List Participant -> List (Maybe Participant) -> List (Maybe Participant)
    derefParticipants' []          ps acc = acc
    derefParticipants' ("*" :: xs) ps acc = map Just ps
    derefParticipants' (x :: xs)   ps acc = derefParticipants' xs ps $ ((derefParticipant x ps) :: acc)

derefEvent : EventRef -> List Event -> Maybe Event
derefEvent _   []        = Nothing
derefEvent ref (x :: xs) = if name x == ref
                              then Just x
                              else derefEvent ref xs

derefState : StateRef -> List State -> Maybe State
derefState _   []        = Nothing
derefState ref (x :: xs) = if name x == ref
                              then Just x
                              else derefState ref xs
export
liftMaybeList : List (Maybe a) -> Maybe (List a)
liftMaybeList [] = Nothing
liftMaybeList xs = Just $ reverse $ foldl (\acc, x => case x of Just x' => x' :: acc; Nothing => acc) [] xs

export
isAllJust : List (Maybe a) -> Bool
isAllJust = foldl (\acc, x => acc && (isJust x)) True

export
unzipEitherList : List (Either a b) -> (List a, List b)
unzipEitherList xs
  = unzipEitherList' xs [] []
  where
    unzipEitherList' : List (Either a b) -> List a -> List b -> (List a, List b)
    unzipEitherList' []                as bs = (reverse as, reverse bs)
    unzipEitherList' ((Left a)  :: xs) as bs = unzipEitherList' xs (a :: as) bs
    unzipEitherList' ((Right b) :: xs) as bs = unzipEitherList' xs as (b :: bs)

--------------
-- Analyser --
--------------

Rule : Type -> Type
Rule ty = Grammar SExp True ty

symbol : String -> Rule String
symbol s
  = terminal ("Expected symbol " ++ (bold s))
             (\x => case x of
                         SymbolAtom s' => if s == s'
                                             then Just s
                                             else Nothing
                         _ => Nothing)

anySymbol : Rule String
anySymbol
  = terminal "Expected symbol"
             (\x => case x of
                         SymbolAtom s => Just s
                         _ => Nothing)

char : Char -> Rule Char
char c
  = terminal ("Expected char " ++ (bold (show c)))
             (\x => case x of
                         CharAtom c' => if c == c'
                                             then Just c
                                             else Nothing
                         _ => Nothing)

anyChar : Rule Char
anyChar
  = terminal "Expected char"
             (\x => case x of
                         CharAtom c => Just c
                         _ => Nothing)

string : String -> Rule String
string s
  = terminal ("Expected string \"" ++ (bold s) ++ "\"")
             (\x => case x of
                         StringAtom s' => if s == s'
                                             then Just s
                                             else Nothing
                         _ => Nothing)

anyString : Rule String
anyString
  = terminal "Expected string"
             (\x => case x of
                         StringAtom s => Just s
                         _ => Nothing)

integer : Rule Int
integer
  = terminal "Expected integer"
             (\x => case x of
                         IntAtom n => Just n
                         _ => Nothing)

real : Rule Double
real
  = terminal "Expected real"
             (\x => case x of
                         RealAtom n => Just n
                         _ => Nothing)

meta : Rule Meta
meta
  = terminal "Expected meta sexp"
             (\x => case x of
                         SExpList ss => case parse meta' ss of
                                             Left _ => Nothing
                                             Right (result, _) => Just result
                         _ => Nothing)
  where
    mvstring : Rule MetaValue
    mvstring
      = do v <- anyString
           pure (MVString v)

    mvlist : Rule MetaValue
    mvlist
      = terminal ("Expected " ++ (bold "list") ++ " sexp")
                 (\x => case x of
                             SExpList ss => case parse mvlist' ss of
                                                 Left _ => Nothing
                                                 Right (v, _) => Just v
                             _ => Nothing)
      where
        mvlist' : Rule MetaValue
        mvlist'
          = do symbol "list" -- must have to consume the following MANY rule
               vs <- many anyString
               pure (MVList vs)

    mvdict : Rule MetaValue
    mvdict
      = terminal ("Expected " ++ (bold "dict") ++ " sexp")
                 (\x => case x of
                             SExpList ss => case parse mvdict' ss of
                                                 Left _ => Nothing
                                                 Right (v, _) => Just v
                             _ => Nothing)
      where
        strtuple : Rule (String, String)
        strtuple
          = terminal ("Expected sexp list")
                     (\x => case x of
                                 SExpList ss => case parse strtuple' ss of
                                                     Left _ => Nothing
                                                     Right (v, _) => Just v
                                 _ => Nothing)
          where
            strtuple' : Rule (String, String)
            strtuple'
              = do k <- anyString
                   v <- anyString
                   pure ((k, v))

        mvdict' : Rule MetaValue
        mvdict'
          = do symbol "dict"
               ts <- many strtuple
               pure (MVDict (foldl (\acc, (x, y) => insert x y acc) SortedMap.empty ts))

    meta' : Rule Meta
    meta'
      = do symbol "meta"
           k <- anyString
           v <- (mvstring <|> mvlist <|> mvdict)
           pure (MkMeta k v)

----------
-- Type --
----------

mutual
  tipe : Rule TipeShadow
  tipe = primtype <|> list <|> dict <|> rekord
    where
      prim : Rule PrimType
      prim = terminal ("Expected one of strings: " ++ (foldl (\ a, e => a ++ " " ++ e) "" primTypeStrs))
                      (\x => case x of
                                  SymbolAtom s => fromString s
                                  _ => Nothing)

      primtype : Rule TipeShadow
      primtype
        = do x <- prim
             pure (TPrimTypeShadow x)

      list : Rule TipeShadow
      list
        = terminal ("Expected " ++ (bold "list") ++ " sexp")
                   (\x => case x of
                               SExpList ss => case parse list' ss of
                                                   Left _ => Nothing
                                                   Right (v, _) => Just v
                               _ => Nothing)
        where
          list' : Rule TipeShadow
          list'
            = do symbol "list"
                 t <- choose anySymbol tipe
                 pure (TListShadow t)

      dict : Rule TipeShadow
      dict
        = terminal ("Expected " ++ (bold "dict") ++ " sexp")
                   (\x => case x of
                               SExpList ss => case parse dict' ss of
                                                   Left _ => Nothing
                                                   Right (v, _) => Just v
                               _ => Nothing)
        where
          dict' : Rule TipeShadow
          dict'
            = do symbol "dict"
                 k <- prim
                 v <- choose anySymbol tipe
                 pure (TDictShadow k v)

      rekord : Rule TipeShadow
      rekord
        = terminal ("Expected " ++ (bold "record") ++ " sexp")
                   (\x => case x of
                               SExpList ss => case parse rekord' ss of
                                                   Left _ => Nothing
                                                   Right (v, _) => Just v
                               _ => Nothing)
        where
          rekord' : Rule TipeShadow
          rekord'
            = do symbol "record"
                 n <- anySymbol
                 ts <- many thz
                 pure (TRecordShadow n ts)

  thz : Rule ParameterShadow
  thz
    = terminal ("Expected " ++ (bold "the") ++ " sexp")
               (\x => case x of
                           SExpList ss => case parse thz' ss of
                                               Left _ => Nothing
                                               Right (result, _) => Just result
                           _ => Nothing)
    where
      thz' : Rule ParameterShadow
      thz'
        = do symbol "the"
             t <- choose anySymbol tipe
             n <- anySymbol
             ms <- many meta
             pure (n, t, if length ms > Z then Just ms else Nothing)

deftype : Rule (Name, TipeShadow)
deftype
  = terminal ("Expected " ++ (bold "deftype") ++ " sexp")
             (\x => case x of
                         SExpList ss => case parse deftype' ss of
                                             Left _ => Nothing
                                             Right (v, _) => Just v
                         _ => Nothing)
  where
    deftype' : Rule (Name, TipeShadow)
    deftype'
      = do symbol "deftype"
           n <- anySymbol
           t <- tipe
           pure (n, t)

-----------
-- Model --
-----------

model : Rule (List ParameterShadow)
model
  = terminal ("Expected model sexp")
             (\x => case x of
                         SExpList ss => case parse model' ss of
                                             Left _ => Nothing
                                             Right (result, _) => Just result
                         _ => Nothing)
  where
    model' : Rule (List ParameterShadow)
    model'
      = do symbol "model"
           xs <- many thz
           pure xs

-----------
-- Event --
-----------
event : Rule EventShadow
event
  = terminal ("Expected event sexp")
             (\x => case x of
                         SExpList ss => case parse event' ss of
                                             Left _ => Nothing
                                             Right (result, _) => Just result
                         _ => Nothing)
  where
    event' : Rule EventShadow
    event'
      = do symbol "event"
           n <- anySymbol
           xs <- many thz
           ms <- many meta
           pure (MkEventShadow n xs (if length ms > Z then Just ms else Nothing))

-----------------
-- Participant --
-----------------

participant : Rule Participant
participant
  = terminal ("Expected participant sexp")
             (\x => case x of
                         SExpList ss => case parse participant' ss of
                                             Left _ => Nothing
                                             Right (result, _) => Just result
                         _ => Nothing)
  where
    participant' : Rule Participant
    participant'
      = do symbol "participant"
           n <- anySymbol
           ms <- many meta
           pure (MkParticipant n (if length ms > Z then Just ms else Nothing))

----------
-- Port --
----------

port : Rule PortShadow
port
  = terminal ("Expected port sexp")
             (\x => case x of
                         SExpList ss => case parse port' ss of
                                             Left _ => Nothing
                                             Right (result, _) => Just result
                         _ => Nothing)
  where
    port' : Rule PortShadow
    port'
      = do symbol "port"
           n <- anySymbol
           t <- many tipe
           pure (MkPortShadow n t)

----------------
-- Expression --
----------------

identifier : Rule Expression
identifier
  = do x <- anySymbol
       pure (IdentifyExpression x)

integerLiteral : Rule Expression
integerLiteral
  = do x <- integer
       pure (IntegerLiteralExpression x)

realLiteral : Rule Expression
realLiteral
  = do x <- real
       pure (RealLiteralExpression x)

charLiteral : Rule Expression
charLiteral
  = do x <- anyChar
       pure (CharLiteralExpression x)

stringLiteral : Rule Expression
stringLiteral
  = do x <- anyString
       pure (StringLiteralExpression x)

booleanLiteral : Rule Expression
booleanLiteral
  = do x <- (symbol "true") <|> (symbol "false")
       pure (BooleanExpression (toBool x))

mutual
  application : Rule Expression
  application
    = terminal ("Expected application sexp list")
               (\x => case x of
                           SExpList ss => case parse application' ss of
                                               Left _ => Nothing
                                               Right (result, _) => Just result
                           _ => Nothing)
    where
      application' : Rule Expression
      application'
        = do fun <- anySymbol
             args <- many expression
             pure (ApplicationExpression fun args)

  expression : Rule Expression
  expression
    = booleanLiteral <|> integerLiteral <|> realLiteral <|> charLiteral <|> stringLiteral <|> identifier <|> application

compare : Rule TestExpression
compare
  = terminal ("Expected comparation sexp list")
             (\x => case x of
                         SExpList ss => case parse compare' ss of
                                             Left _ => Nothing
                                             Right (result, _) => Just result
                         _ => Nothing)
  where
    operation : Rule CompareOperation
    operation = terminal ("Expected one of symbols: " ++ (foldl (\ a, e => a ++ " " ++ e) "" primTypeStrs))
                         (\x => case x of
                                     SymbolAtom s => fromString s
                                     _ => Nothing)

    compare' : Rule TestExpression
    compare'
      = do op <- operation
           lexp <- expression
           rexp <- expression
           pure (CompareExpression op lexp rexp)

primitiveBool : Rule TestExpression
primitiveBool
  = terminal ("Expected sexp list of application or identifier or bool")
             (\x => case x of
                         SymbolAtom "true" => Just (PrimitiveTestExpression (BooleanExpression True))
                         SymbolAtom "false" => Just (PrimitiveTestExpression (BooleanExpression False))
                         SymbolAtom i => Just (PrimitiveTestExpression (IdentifyExpression i))
                         SExpList _ => case parse application [x] of
                                            Left _ => Nothing
                                            Right (result, _) => Just (PrimitiveTestExpression result)
                         _ => Nothing)

mutual
  unaryBool : Rule TestExpression
  unaryBool
    = terminal ("Expected unary bool sexp list")
               (\x => case x of
                           SExpList ss => case parse unaryBool' ss of
                                               Left _ => Nothing
                                               Right (result, _) => Just result
                           _ => Nothing)
    where
      operation : Rule UnaryBoolOperation
      operation = terminal ("Expected " ++ (bold "not"))
                           (\x => case x of
                                       SymbolAtom "not" => Just NotBoolOperation
                                       _ => Nothing)

      unaryBool' : Rule TestExpression
      unaryBool'
        = do op <- operation
             exp <- testExpression
             pure (UnaryTestExpression op exp)

  binaryBool : Rule TestExpression
  binaryBool
    = terminal ("Expected binary bool sexp list")
               (\x => case x of
                           SExpList ss => case parse binaryBool' ss of
                                               Left _ => Nothing
                                               Right (result, _) => Just result
                           _ => Nothing)
    where
      operation : Rule BinaryBoolOperation
      operation = terminal ("Expected " ++ (bold "and") ++ "/" ++ (bold "or"))
                           (\x => case x of
                                       SymbolAtom "and" => Just AndBoolOperation
                                       SymbolAtom "or" => Just OrBoolOperation
                                       _ => Nothing)

      binaryBool' : Rule TestExpression
      binaryBool'
        = do op <- operation
             lexp <- testExpression
             rexp <- testExpression
             pure (BinaryTestExpression op lexp rexp)

  testExpression : Rule TestExpression
  testExpression = unaryBool <|> binaryBool <|> compare <|> primitiveBool

------------
-- Action --
------------

action : Rule ActionShadow
action
  = terminal ("Expected sexp list")
             (\x => case x of
                         SExpList ss => case parse action' ss of
                                             Left _ => Nothing
                                             Right (result, _) => Just result
                         _ => Nothing)
  where
    assignment : Rule ActionShadow
    assignment
      = do symbol "set!"
           i <- identifier
           e <- expression
           pure (AssignmentActionShadow i e)

    output : Rule ActionShadow
    output
      = do symbol "output"
           n  <- anySymbol
           es <- many expression
           pure (OutputActionShadow n es)

    action' : Rule ActionShadow
    action' = assignment <|> output

-----------
-- State --
-----------

onEnter : Rule (List ActionShadow)
onEnter
  = terminal ("Expected on-enter sexp")
             (\x => case x of
                         SExpList ss => case parse onEnter' ss of
                                             Left _ => Nothing
                                             Right (result, _) => Just result
                         _ => Nothing)
  where
    onEnter' : Rule (List ActionShadow)
    onEnter'
      = do symbol "on-enter"
           xs <- many action
           pure xs

onExit : Rule (List ActionShadow)
onExit
  = terminal ("Expected on-enter sexp")
             (\x => case x of
                         SExpList ss => case parse onExit' ss of
                                             Left _ => Nothing
                                             Right (result, _) => Just result
                         _ => Nothing)
  where
    onExit' : Rule (List ActionShadow)
    onExit'
      = do symbol "on-exit"
           xs <- many action
           pure xs

state : Rule StateShadow
state
  = terminal ("Expected state sexp")
             (\x => case x of
                         SExpList ss => case parse state' ss of
                                             Left _ => Nothing
                                             Right (result, _) => Just result
                         _ => Nothing)
  where
    item : Rule (Either (List ActionShadow) (Either (List ActionShadow) Meta))
    item = choose onEnter (choose onExit meta)

    unzipItems : List (Either (List ActionShadow) (Either (List ActionShadow) Meta)) -> ((List (List ActionShadow)), (List (List ActionShadow)), List Meta) -> ((List (List ActionShadow)), (List (List ActionShadow)), List Meta)
    unzipItems [] (ens, exs, ms) = (reverse ens, reverse exs, ms)
    unzipItems (x :: xs) (ens, exs, ms) = case x of
                                               Left en => unzipItems xs (en :: ens, exs, ms)
                                               Right x1 => case x1 of
                                                                Left ex => unzipItems xs (ens, ex :: exs, ms)
                                                                Right m => unzipItems xs (ens, exs, m :: ms)
    toMaybeElem : List a -> Maybe a
    toMaybeElem [] = Nothing
    toMaybeElem (x :: xs) = Just x

    state' : Rule StateShadow
    state'
      = do symbol "state"
           n <- anySymbol
           is <- many item
           let uz = unzipItems is ([], [], [])
           pure (MkStateShadow n
                               (toMaybeElem (fst uz))
                               (toMaybeElem ((fst . snd) uz))
                               (toMaybe ((snd . snd) uz)))

----------------
-- Transition --
----------------

transitionAction : Rule (List ActionShadow)
transitionAction
  = terminal ("Expected action sexp")
             (\x => case x of
                         SExpList ss => case parse transitionAction' ss of
                                             Left _ => Nothing
                                             Right (result, _) => Just result
                         _ => Nothing)
  where
    transitionAction' : Rule (List ActionShadow)
    transitionAction'
      = do symbol "action"
           xs <- many action
           pure xs

fromTo : Rule (StateRef, StateRef)
fromTo
  = terminal ("Expected from-to sexp")
             (\x => case x of
                         SExpList ss => case parse fromTo' ss of
                                             Left _ => Nothing
                                             Right (result, _) => Just result
                         _ => Nothing)
  where
    fromTo' : Rule (StateRef, StateRef)
    fromTo'
      = do symbol "from-to"
           s <- anySymbol
           d <- anySymbol
           pure (s, d)

guard : Rule TestExpression
guard
  = terminal ("Expected where sexp")
             (\x => case x of
                         SExpList ss => case parse guard' ss of
                                             Left _ => Nothing
                                             Right (result, _) => Just result
                         _ => Nothing)
  where
    guard' : Rule TestExpression
    guard'
      = do symbol "where"
           b <- testExpression
           pure b

trigger : Rule TriggerShadow
trigger
  = terminal ("Expected trigger sexp")
             (\x => case x of
                         SExpList ss => case parse trigger' ss of
                                             Left _ => Nothing
                                             Right (result, _) => Just result
                         _ => Nothing)
  where
    trigger' : Rule TriggerShadow
    trigger'
      = trigger'' <|> trigger'''
      where
        plist : Rule (List ParticipantRef)
        plist
          = terminal ("Expected list sexp")
                     (\x => case x of
                                 SExpList ss => case parse plist' ss of
                                                     Left _ => Nothing
                                                     Right (result, _) => Just result
                                 _ => Nothing)
          where
            plist' : Rule (List ParticipantRef)
            plist'
              = do symbol "list" -- must have to consume the following MANY rule
                   vs <- many anySymbol
                   pure vs

        trigger'' : Rule TriggerShadow
        trigger''
          = do symbol "trigger"
               p <- anySymbol
               e <- anySymbol
               g <- optional guard
               as <- optional transitionAction
               pure (MkTriggerShadow [p] e g as)

        trigger''' : Rule TriggerShadow
        trigger'''
          = do symbol "trigger"
               ps <- plist
               e <- anySymbol
               g <- optional guard
               as <- optional transitionAction
               pure (MkTriggerShadow ps e g as)

transition : Rule TransitionShadow
transition
  = terminal ("Expected transition sexp")
             (\x => case x of
                         SExpList ss => case parse transition' ss of
                                             Left _ => Nothing
                                             Right (result, _) => Just result
                         _ => Nothing)
  where
    transition' : Rule TransitionShadow
    transition'
      = do symbol "transition"
           sd <- fromTo
           ts <- many trigger
           pure (MkTransitionShadow (fst sd) (snd sd) ts)

---------
-- FSM --
---------

fsm : Rule Fsm
fsm
  = do symbol "fsm"
       n <- anySymbol
       is <- many item
       let uz = unzipItems is ([], [], [], [], [], [], [], [])
       case deshadowDefType $ (Builtin.fst . snd . snd . snd . snd . snd . snd) uz of
            Left e => fail e
            Right cts => let (mers, m) = unzipEitherList $ map (deshadowParameter cts) $ fst uz in
                             if length mers > Z
                                then do fail ("Unsolved types in model:\n" ++ (List.join "\n" mers))
                                else let (eers, es) = unzipEitherList $ map (deshadowEvent cts) $ (Builtin.fst . snd . snd) uz in
                                         if length eers > Z
                                            then do fail ("Unsolved types in events:\n" ++ (List.join "\n" eers))
                                            else let (pters, pts) = unzipEitherList $ map (deshadowPort cts) $ (snd . snd . snd . snd . snd . snd . snd) uz in
                                                     if length pters > Z
                                                        then do fail ("Unsolved types in ports:\n" ++ (List.join "\n" pters))
                                                        else let (sers, ss) = unzipEitherList $ map (deshadowState pts) $ (Builtin.fst . snd . snd . snd) uz in
                                                                 if length sers > Z
                                                                    then do fail ("Unsolved error in states:\n" ++ (List.join "\n" sers))
                                                                    else let ps = (fst . snd) uz
                                                                             ms = toMaybe $ (Builtin.fst . snd . snd . snd . snd . snd) uz
                                                                             (ters, ts) = unzipEitherList $ map (deshadowTransition ps es ss pts) ((Builtin.fst . snd . snd . snd . snd) uz) in
                                                                             if length ters > Z
                                                                                then do fail ("Unsolved error:\n" ++ (List.join "\n" ters))
                                                                                else case constructFsm n m ps es ss ts ms pts of
                                                                                          Right fsm => do pure fsm
                                                                                          Left err => do fail err

  where
    liftFromMaybe : Maybe a -> Either String (Maybe a)
    liftFromMaybe x = Right x

    unzipItems : List (Either (List ParameterShadow) (Either Participant (Either EventShadow (Either StateShadow (Either TransitionShadow (Either Meta (Either (Name, TipeShadow) PortShadow))))))) -> (List ParameterShadow, List Participant, List EventShadow, List StateShadow, List TransitionShadow, List Meta, List (Name, TipeShadow), List PortShadow) -> (List ParameterShadow, List Participant, List EventShadow, List StateShadow, List TransitionShadow, List Meta, List (Name, TipeShadow), List PortShadow)
    unzipItems []        (m, ps, es, ss, ts, ms, ds, pts) = (m, reverse ps, reverse es, reverse ss, reverse ts, ms, ds, pts)
    unzipItems (x :: xs) (m, ps, es, ss, ts, ms, ds, pts) = case x of
                                                            Left m' => unzipItems xs (m', ps, es, ss, ts, ms, ds, pts)
                                                            Right x0 => case x0 of
                                                                             Left p => unzipItems xs (m, p :: ps, es, ss, ts, ms, ds, pts)
                                                                             Right x1 => case x1 of
                                                                                              Left e => unzipItems xs (m, ps, e :: es, ss, ts, ms, ds, pts)
                                                                                              Right x2 => case x2 of
                                                                                                               Left s => unzipItems xs (m, ps, es, s :: ss, ts, ms, ds, pts)
                                                                                                               Right x3 => case x3 of
                                                                                                                                Left t => unzipItems xs (m, ps, es, ss, t :: ts, ms, ds, pts)
                                                                                                                                Right x4 => case x4 of
                                                                                                                                                 Left m' => unzipItems xs (m, ps, es, ss, ts, m' :: ms, ds, pts)
                                                                                                                                                 Right x5 => case x5 of
                                                                                                                                                                  Left d => unzipItems xs (m, ps, es, ss, ts, ms, d :: ds, pts)
                                                                                                                                                                  Right pt => unzipItems xs (m, ps, es, ss, ts, ms, ds, pt :: pts)

    item : Rule (Either (List ParameterShadow) (Either Participant (Either EventShadow (Either StateShadow (Either TransitionShadow (Either Meta (Either (Name, TipeShadow) PortShadow)))))))
    item
      = do x <- choose model (choose participant (choose event (choose state (choose transition (choose meta (choose deftype port))))))
           pure x

    deshadowAction : List Port -> ActionShadow -> Either String Action
    deshadowAction _                      (AssignmentActionShadow lhs rhs) = Right (AssignmentAction lhs rhs)
    deshadowAction []                     (OutputActionShadow pr _)        = Left ("Missing port " ++ pr)
    deshadowAction (p@(MkPort n _) :: ps) a@(OutputActionShadow pr es)     = if n == pr
                                                                                then Right (OutputAction p es)
                                                                                else deshadowAction ps a

    deshadowState : List Port -> StateShadow -> Either String State
    deshadowState pts (MkStateShadow n (Just enas) (Just exas) ms)
      = let (eners, enas') = unzipEitherList $ map (deshadowAction pts) enas
            (exers, exas') = unzipEitherList $ map (deshadowAction pts) exas in
            if length eners > Z
               then Left (List.join "\n" eners)
               else if length exers > Z
                       then Left (List.join "\n" exers)
                       else Right (MkState n (Just enas') (Just exas') ms)
    deshadowState pts (MkStateShadow n (Just as) Nothing ms)
      = let (ers, as') = unzipEitherList $ map (deshadowAction pts) as in
            if length ers > Z
               then Left (List.join "\n" ers)
               else Right (MkState n (Just as') Nothing ms)
    deshadowState pts (MkStateShadow n Nothing (Just as) ms)
      = let (ers, as') = unzipEitherList $ map (deshadowAction pts) as in
            if length ers > Z
               then Left (List.join "\n" ers)
               else Right (MkState n Nothing (Just as') ms)
    deshadowState pts (MkStateShadow n Nothing Nothing ms)
      = Right (MkState n Nothing Nothing ms)

    deshadowTrigger : List Participant -> List Event -> List Port -> TriggerShadow -> Either String Trigger
    deshadowTrigger ps es pts (MkTriggerShadow prs er g (Just as))
      = let (errs, as') = unzipEitherList $ map (deshadowAction pts) as in
            if length errs > Z
               then Left $ List.join "\n" errs
               else do Just e <- liftFromMaybe $ derefEvent er es
                       | Nothing => Left ("Missing event " ++ er)
                       Just ps' <- liftFromMaybe $ liftMaybeList $ filter isJust $ derefParticipants prs ps
                       | Nothing => Left ("Missing participants " ++ (List.join ", " prs))
                       Just ps'' <- liftFromMaybe $ List1.fromList ps'
                       | Nothing => Left ("Require one " ++ (bold "participant") ++ " at least")
                       pure (MkTrigger ps'' e g (List1.fromList as'))
    deshadowTrigger ps es pts (MkTriggerShadow prs er g Nothing)
      = do Just e <- liftFromMaybe $ derefEvent er es
           | Nothing => Left ("Missing event " ++ er)
           Just ps' <- liftFromMaybe $ liftMaybeList $ filter isJust $ derefParticipants prs ps
           | Nothing => Left ("Missing participants " ++ (List.join ", " prs))
           Just ps'' <- liftFromMaybe $ List1.fromList ps'
           | Nothing => Left ("Require one " ++ (bold "participant") ++ " at least")
           pure (MkTrigger ps'' e g Nothing)

    deshadowTransition : List Participant -> List Event -> List State -> List Port -> TransitionShadow -> Either String Transition
    deshadowTransition ps es ss pts (MkTransitionShadow sr dr ts)
      = let (errs, ts') = unzipEitherList $ map (deshadowTrigger ps es pts) ts in
            if length errs > Z
               then Left $ List.join "\n" errs
               else do Just src <- liftFromMaybe $ derefState sr ss
                       | Nothing => Left ("Missing source state " ++ sr)
                       Just dst <- liftFromMaybe $ derefState dr ss
                       | Nothing => Left ("Missing destination state " ++ sr)
                       Just ts'' <- liftFromMaybe $ List1.fromList ts'
                       | Nothing => Left ("Require one trigger in transition from " ++ sr ++ " to " ++ dr)
                       pure (MkTransition src dst ts'')

    mutual
      deshadowParameter : SortedMap String Tipe -> ParameterShadow -> Either String Parameter
      deshadowParameter env (n, Left ref, ms) = case lookup ref env of
                                                     Nothing => Left ref
                                                     Just t => Right (n, t, ms)
      deshadowParameter env (n, Right t, ms)  = case shadowToTipe env t of
                                                     Left e => Left e
                                                     Right t' => Right (n, t', ms)

      shadowToTipe : SortedMap String Tipe -> TipeShadow -> Either String Tipe
      shadowToTipe env (TPrimTypeShadow t)        = Right (TPrimType t)
      shadowToTipe env (TListShadow (Left ref))   = case lookup ref env of
                                                         Nothing => Left ref
                                                         Just t => Right (TList t)
      shadowToTipe env (TListShadow (Right t))    = case shadowToTipe env t of
                                                         Left e => Left e
                                                         Right t' => Right (TList t')
      shadowToTipe env (TDictShadow k (Left ref)) = case lookup ref env of
                                                         Nothing => Left ref
                                                         Just v => Right (TDict k v)
      shadowToTipe env (TDictShadow k (Right v))  = case shadowToTipe env v of
                                                         Left e => Left e
                                                         Right v' => Right (TDict k v')
      shadowToTipe env (TArrowShadow f t)         = case shadowToTipe env f of
                                                         Left e => Left e
                                                         Right f' => case shadowToTipe env t of
                                                                          Left e' => Left e'
                                                                          Right t' => Right (TArrow f' t')
      shadowToTipe env TUnitShadow                = Right TUnit
      shadowToTipe env (TRecordShadow n ps)       = let (es, ps') = unzipEitherList (map (deshadowParameter env) ps) in
                                                        if length es > Z
                                                           then Left $ foldl (\acc, x => acc ++ " " ++ x ) "" es
                                                           else Right (TRecord n ps')

    deshadowDefType : List (Name, TipeShadow) -> Either String (SortedMap Name Tipe)
    deshadowDefType ds
      = deshadowDefType' ds [] (length ds) $ foldl (\acc, x => case PrimType.fromString x of Just t => insert x (TPrimType t) acc; Nothing => acc) empty primTypeStrs
      where
        deshadowDefType' : List (Name, TipeShadow) -> List (Name, TipeShadow) -> Nat -> SortedMap Name Tipe -> Either String (SortedMap Name Tipe)
        deshadowDefType' []               []       _   acc = Right acc
        deshadowDefType' []               unsolved Z   acc = Left ("Unsolved customized types: " ++ (foldl (\a, (n, _) => a ++ " " ++ (bold n)) "" unsolved))
        deshadowDefType' []               unsolved cnt acc = deshadowDefType' unsolved [] (minus cnt 1) acc
        deshadowDefType' (d@(n, t) :: xs) unsolved cnt acc = case shadowToTipe acc t of
                                                                  Left  _  => deshadowDefType' xs (d :: unsolved) cnt acc
                                                                  Right t' => deshadowDefType' xs unsolved cnt $ insert n t' acc

    deshadowEvent : SortedMap Name Tipe -> EventShadow -> Either String Event
    deshadowEvent env (MkEventShadow n ps ms)
      = let (es, ps') = unzipEitherList $ map (deshadowParameter env) ps in
            if length es > Z
               then Left (List.join "\n" es)
               else Right (MkEvent n ps' ms)

    deshadowPort : SortedMap Name Tipe -> PortShadow -> Either String Port
    deshadowPort env (MkPortShadow n ts)
      = let (es, ts') = unzipEitherList $ map (shadowToTipe env) ts in
            if length es > Z
               then Left (List.join "\n" es)
               else Right (MkPort n (constructTArrow (reverse ts') TUnit))

    constructFsm : String -> List Parameter -> List Participant -> List Event -> List State -> List Transition -> Maybe (List Meta) -> List Port -> Either String Fsm
    constructFsm n m ps es ss ts ms pts
      = do Just ps' <- liftFromMaybe $ List1.fromList ps
           | Nothing => Left ("Require one " ++ (bold "participant") ++ " at least")
           Just es' <- liftFromMaybe $ List1.fromList es
           | Nothing => Left ("Require one " ++ (bold "event") ++ " at least")
           Just ss' <- liftFromMaybe $ List1.fromList ss
           | Nothing => Left ("Require one " ++ (bold "state") ++ " at least")
           Just ts' <- liftFromMaybe $ List1.fromList ts
           | Nothing => Left ("Require one " ++ (bold "transition") ++ " at least")
           pure (MkFsm n m pts ps' es' ss' ts' ms)

---------
-- API --
---------

export
analyse : SExp -> Either (ParseError SExp) (Fsm, List SExp)
analyse (SExpList sexp) = parse fsm sexp
analyse _               = Left (Error ("Expected " ++ (bold "fsm") ++ "sexp") [])
