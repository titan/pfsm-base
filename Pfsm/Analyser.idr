module Pfsm.Analyser

import Control.Delayed
import Data.List
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

record TriggerShadow where
  constructor MkTriggerShadow
  participants: List ParticipantRef
  event: EventRef
  guard: Maybe TestExpression
  actions: Maybe (List Action)

record TransitionShadow where
  constructor MkTransitionShadow
  src: StateRef
  dst: StateRef
  triggers: List TriggerShadow

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

liftMaybeList : List (Maybe a) -> Maybe (List a)
liftMaybeList [] = Nothing
liftMaybeList xs = Just $ foldl (\acc, x => case x of Just x' => x' :: acc; Nothing => acc) [] xs

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

tipe : Rule Tipe
tipe = primtype <|> list <|> dict
  where
    prim : Rule PrimType
    prim = terminal ("Expected one of strings: " ++ (foldl (\ a, e => a ++ " " ++ e) "" primTypeStrs))
                    (\x => case x of
                                SymbolAtom s => fromString s
                                _ => Nothing)

    primtype : Rule Tipe
    primtype
      = do x <- prim
           pure (TPrimType x)

    list : Rule Tipe
    list
      = terminal ("Expected " ++ (bold "list") ++ " sexp")
                 (\x => case x of
                             SExpList ((SymbolAtom "list") :: ss) => case parse tipe ss of
                                                                          Left _ => Nothing
                                                                          Right (t, _) => Just (TList t)
                             _ => Nothing)

    dict : Rule Tipe
    dict
      = terminal ("Expected " ++ (bold "dict") ++ " sexp")
                 (\x => case x of
                             SExpList ((SymbolAtom "dict") :: ss) => case parse prim ss of
                                                                          Left _ => Nothing
                                                                          Right (p, sss) => case parse tipe sss of
                                                                                                 Left _ => Nothing
                                                                                                 Right (t, _) => Just (TDict p t)
                             _ => Nothing)

thz : Rule Parameter
thz
  = terminal ("Expected " ++ (bold "the") ++ " sexp")
             (\x => case x of
                         SExpList ss => case parse thz' ss of
                                             Left _ => Nothing
                                             Right (result, _) => Just result
                         _ => Nothing)
  where
    thz' : Rule Parameter
    thz'
      = do symbol "the"
           t <- tipe
           n <- anySymbol
           ms <- many meta
           pure (n, t, if length ms > Z then Just ms else Nothing)

-----------
-- Model --
-----------

model : Rule (List Parameter)
model
  = terminal ("Expected model sexp")
             (\x => case x of
                         SExpList ss => case parse model' ss of
                                             Left _ => Nothing
                                             Right (result, _) => Just result
                         _ => Nothing)
  where
    model' : Rule (List Parameter)
    model'
      = do symbol "model"
           xs <- many thz
           pure xs

-----------
-- Event --
-----------
event : Rule Event
event
  = terminal ("Expected event sexp")
             (\x => case x of
                         SExpList ss => case parse event' ss of
                                             Left _ => Nothing
                                             Right (result, _) => Just result
                         _ => Nothing)
  where
    event' : Rule Event
    event'
      = do symbol "event"
           n <- anySymbol
           xs <- many thz
           ms <- many meta
           pure (MkEvent n xs (if length ms > Z then Just ms else Nothing))

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
    = booleanLiteral <|> integerLiteral <|> realLiteral <|> stringLiteral <|> identifier <|> application

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

action : Rule Action
action
  = terminal ("Expected sexp list")
             (\x => case x of
                         SExpList ss => case parse action' ss of
                                             Left _ => Nothing
                                             Right (result, _) => Just result
                         _ => Nothing)
  where
    assignment : Rule Action
    assignment
      = do symbol "set!"
           i <- identifier
           e <- expression
           pure (AssignmentAction i e)

    output : Rule Action
    output
      = do symbol "output"
           n  <- anySymbol
           es <- many expression
           pure (OutputAction n es)

    action' : Rule Action
    action' = assignment <|> output

-----------
-- State --
-----------

onEnter : Rule (List Action)
onEnter
  = terminal ("Expected on-enter sexp")
             (\x => case x of
                         SExpList ss => case parse onEnter' ss of
                                             Left _ => Nothing
                                             Right (result, _) => Just result
                         _ => Nothing)
  where
    onEnter' : Rule (List Action)
    onEnter'
      = do symbol "on-enter"
           xs <- many action
           pure xs

onExit : Rule (List Action)
onExit
  = terminal ("Expected on-enter sexp")
             (\x => case x of
                         SExpList ss => case parse onExit' ss of
                                             Left _ => Nothing
                                             Right (result, _) => Just result
                         _ => Nothing)
  where
    onExit' : Rule (List Action)
    onExit'
      = do symbol "on-exit"
           xs <- many action
           pure xs

state : Rule State
state
  = terminal ("Expected state sexp")
             (\x => case x of
                         SExpList ss => case parse state' ss of
                                             Left _ => Nothing
                                             Right (result, _) => Just result
                         _ => Nothing)
  where
    item : Rule (Either (List Action) (Either (List Action) Meta))
    item = choose onEnter (choose onExit meta)

    unzipItems : List (Either (List Action) (Either (List Action) Meta)) -> ((List (List Action)), (List (List Action)), List Meta) -> ((List (List Action)), (List (List Action)), List Meta)
    unzipItems [] (ens, exs, ms) = (reverse ens, reverse exs, ms)
    unzipItems (x :: xs) (ens, exs, ms) = case x of
                                               Left en => unzipItems xs (en :: ens, exs, ms)
                                               Right x1 => case x1 of
                                                                Left ex => unzipItems xs (ens, ex :: exs, ms)
                                                                Right m => unzipItems xs (ens, exs, m :: ms)
    toMaybeElem : List a -> Maybe a
    toMaybeElem [] = Nothing
    toMaybeElem (x :: xs) = Just x

    state' : Rule State
    state'
      = do symbol "state"
           n <- anySymbol
           is <- many item
           let uz = unzipItems is ([], [], [])
           pure (MkState n
                         (toMaybeElem (fst uz))
                         (toMaybeElem ((fst . snd) uz))
                         (toMaybe ((snd . snd) uz)))

----------------
-- Transition --
----------------

transitionAction : Rule (List Action)
transitionAction
  = terminal ("Expected action sexp")
             (\x => case x of
                         SExpList ss => case parse transitionAction' ss of
                                             Left _ => Nothing
                                             Right (result, _) => Just result
                         _ => Nothing)
  where
    transitionAction' : Rule (List Action)
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
  = terminal ("Expected fsm sexp")
             (\x => case x of
                         SExpList ss => case parse fsm' ss of
                                             Left _ => Nothing
                                             Right (result, _) => Just result
                         _ => Nothing)
  where

    unzipItems : List (Either (List Parameter) (Either Participant (Either Event (Either State (Either TransitionShadow Meta))))) -> (List Parameter, List Participant, List Event, List State, List TransitionShadow, List Meta) -> (List Parameter, List Participant, List Event, List State, List TransitionShadow, List Meta)
    unzipItems []        (m, ps, es, ss, ts, ms) = (m, reverse ps, reverse es, reverse ss, reverse ts, ms)
    unzipItems (x :: xs) (m, ps, es, ss, ts, ms) = case x of
                                                        Left m' => unzipItems xs (m', ps, es, ss, ts, ms)
                                                        Right x0 => case x0 of
                                                                         Left p => unzipItems xs (m, p :: ps, es, ss, ts, ms)
                                                                         Right x1 => case x1 of
                                                                                          Left e => unzipItems xs (m, ps, e :: es, ss, ts, ms)
                                                                                          Right x2 => case x2 of
                                                                                                           Left s => unzipItems xs (m, ps, es, s :: ss, ts, ms)
                                                                                                           Right x3 => case x3 of
                                                                                                                            Left t => unzipItems xs (m, ps, es, ss, t :: ts, ms)
                                                                                                                            Right m' => unzipItems xs (m, ps, es, ss, ts, m' :: ms)

    item : Rule (Either (List Parameter) (Either Participant (Either Event (Either State (Either TransitionShadow Meta)))))
    item
      = do x <- choose model (choose participant (choose event (choose state (choose transition meta))))
           pure x

    unshadowTrigger : List Participant -> List Event -> TriggerShadow -> Maybe Trigger
    unshadowTrigger ps es (MkTriggerShadow prs er g as)
      = do ps' <- liftMaybeList $ filter isJust $ derefParticipants prs ps
           e <- derefEvent er es
           pure (MkTrigger ps' e g as)

    unshadowTransition : List Participant -> List Event -> List State -> TransitionShadow -> Maybe Transition
    unshadowTransition ps es ss (MkTransitionShadow sr dr ts)
      = let src = derefState sr ss
            dst = derefState dr ss
            ts' = map (unshadowTrigger ps es) ts in
            if length (filter (\x => not (isJust x)) ts') > Z
               then Nothing
               else do src <- derefState sr ss
                       dst <- derefState dr ss
                       ts'' <- liftMaybeList $ filter isJust ts'
                       pure (MkTransition src dst ts'')

    fsm' : Rule Fsm
    fsm'
      = do symbol "fsm"
           n <- anySymbol
           is <- many item
           let uz = unzipItems is ([], [], [], [], [], [])
           let m  = fst uz
           let ps = (fst . snd) uz
           let es = (fst . snd . snd) uz
           let ss = (fst . snd . snd . snd) uz
           let ts = map (unshadowTransition ps es ss) ((fst . snd . snd . snd . snd) uz)
           let ms = toMaybe $ (snd . snd . snd . snd . snd) uz
           let tt = filter isJust ts
           if length ts == length tt
              then pure (MkFsm n m ps es ss (fromMaybe [] (liftMaybeList tt)) ms)
              else fail "ParticipantRef, StateRef or EventRef error"

---------
-- API --
---------

export
analyse : SExp -> Either (ParseError SExp) (Fsm, List SExp)
analyse sexp
  = parse fsm [sexp]
