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


mutual
  data TipeShadow = TPrimTypeShadow PrimType
                  | TListShadow (Either String TipeShadow)
                  | TDictShadow PrimType (Either String TipeShadow)
                  | TArrowShadow TipeShadow TipeShadow
                  | TRecordShadow (List ParameterShadow)
                  | TUnitShadow

  ParameterShadow : Type
  ParameterShadow = (Name, Either String TipeShadow, Maybe (List Meta))

record EventShadow where
  constructor MkEventShadow
  name: Name
  params: List ParameterShadow
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

liftMaybeList : List (Maybe a) -> Maybe (List a)
liftMaybeList [] = Nothing
liftMaybeList xs = Just $ foldl (\acc, x => case x of Just x' => x' :: acc; Nothing => acc) [] xs

isAllJust : List (Maybe a) -> Bool
isAllJust = foldl (\acc, x => acc && (isJust x)) True

liftEitherList : List (Either a b) -> (List a, List b)
liftEitherList xs
  = liftEitherList' xs [] []
  where
    liftEitherList' : List (Either a b) -> List a -> List b -> (List a, List b)
    liftEitherList' []                as bs = (as, bs)
    liftEitherList' ((Left a)  :: xs) as bs = liftEitherList' xs (a :: as) bs
    liftEitherList' ((Right b) :: xs) as bs = liftEitherList' xs as (b :: bs)

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
                 ts <- many thz
                 pure (TRecordShadow ts)

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
  = do symbol "fsm"
       n <- anySymbol
       is <- many item
       let uz = unzipItems is ([], [], [], [], [], [], [])
       case deshadowDefType $ (snd . snd . snd . snd . snd . snd) uz of
            Left e => fail e
            Right cts => let (ers, m) = liftEitherList $ map (deshadowParameter cts) $ fst uz in
                             if length ers > Z
                                then do fail ("Unsolved types:" ++ (foldl (\a, x => a ++ " " ++ (bold x)) "" ers) ++ " in model")
                                else let (ers', es) = liftEitherList $ map (deshadowEvent cts) $ (Builtin.fst . snd . snd) uz in
                                         if length ers' > Z
                                            then do fail ("Unsolved types:" ++ (foldl (\a, x => a ++ " " ++ (bold x)) "" ers') ++ " in events")
                                            else let ps = (fst . snd) uz
                                                     ss = (fst . snd . snd . snd) uz
                                                     ts = map (deshadowTransition ps es ss) ((fst . snd . snd . snd . snd) uz)
                                                     ms = toMaybe $ (Builtin.fst . snd . snd . snd . snd . snd) uz
                                                     tt = filter isJust ts in
                                                     if isAllJust ts
                                                        then case constructFsm n m ps es ss tt ms of
                                                                  Right fsm => do pure fsm
                                                                  Left err => do fail err
                                                        else do fail "ParticipantRef, StateRef or EventRef error"

  where

    unzipItems : List (Either (List ParameterShadow) (Either Participant (Either EventShadow (Either State (Either TransitionShadow (Either Meta (Name, TipeShadow))))))) -> (List ParameterShadow, List Participant, List EventShadow, List State, List TransitionShadow, List Meta, List (Name, TipeShadow)) -> (List ParameterShadow, List Participant, List EventShadow, List State, List TransitionShadow, List Meta, List (Name, TipeShadow))
    unzipItems []        (m, ps, es, ss, ts, ms, ds) = (m, reverse ps, reverse es, reverse ss, reverse ts, ms, ds)
    unzipItems (x :: xs) (m, ps, es, ss, ts, ms, ds) = case x of
                                                            Left m' => unzipItems xs (m', ps, es, ss, ts, ms, ds)
                                                            Right x0 => case x0 of
                                                                             Left p => unzipItems xs (m, p :: ps, es, ss, ts, ms, ds)
                                                                             Right x1 => case x1 of
                                                                                              Left e => unzipItems xs (m, ps, e :: es, ss, ts, ms, ds)
                                                                                              Right x2 => case x2 of
                                                                                                               Left s => unzipItems xs (m, ps, es, s :: ss, ts, ms, ds)
                                                                                                               Right x3 => case x3 of
                                                                                                                                Left t => unzipItems xs (m, ps, es, ss, t :: ts, ms, ds)
                                                                                                                                Right x4 => case x4 of
                                                                                                                                                 Left m' => unzipItems xs (m, ps, es, ss, ts, m' :: ms, ds)
                                                                                                                                                 Right d => unzipItems xs (m, ps, es, ss, ts, ms, d :: ds)

    item : Rule (Either (List ParameterShadow) (Either Participant (Either EventShadow (Either State (Either TransitionShadow (Either Meta (Name, TipeShadow)))))))
    item
      = do x <- choose model (choose participant (choose event (choose state (choose transition (choose meta deftype)))))
           pure x

    deshadowTrigger : List Participant -> List Event -> TriggerShadow -> Maybe Trigger
    deshadowTrigger ps es (MkTriggerShadow prs er g as)
      = do ps' <- liftMaybeList $ filter isJust $ derefParticipants prs ps
           ps'' <- List1.fromList ps'
           e <- derefEvent er es
           let as'' = case as of
                          Just as' => List1.fromList as'
                          Nothing => Nothing
           pure (MkTrigger ps'' e g as'')

    deshadowTransition : List Participant -> List Event -> List State -> TransitionShadow -> Maybe Transition
    deshadowTransition ps es ss (MkTransitionShadow sr dr ts)
      = let src = derefState sr ss
            dst = derefState dr ss
            ts' = map (deshadowTrigger ps es) ts in
            if length (filter (\x => not (isJust x)) ts') > Z
               then Nothing
               else do src <- derefState sr ss
                       dst <- derefState dr ss
                       ts'' <- liftMaybeList $ filter isJust ts'
                       ts''' <- List1.fromList ts''
                       pure (MkTransition src dst ts''')

    mutual
      deshadowParameter : SortedMap String Tipe -> ParameterShadow -> Either String Parameter
      deshadowParameter env (n, Left ref, ms) = case lookup ref env of
                                                     Nothing => Left ref
                                                     Just t => Right (n, t, ms)
      deshadowParameter env (n, Right t, ms)  = case shadowToTipe env n t of
                                                     Left e => Left e
                                                     Right t' => Right (n, t', ms)

      shadowToTipe : SortedMap String Tipe -> Name -> TipeShadow -> Either String Tipe
      shadowToTipe env n (TPrimTypeShadow t) = Right (TPrimType t)
      shadowToTipe env n (TListShadow (Left ref))   = case lookup ref env of
                                                           Nothing => Left ref
                                                           Just t => Right (TList t)
      shadowToTipe env n (TListShadow (Right t))    = case shadowToTipe env n t of
                                                           Left e => Left e
                                                           Right t' => Right (TList t')
      shadowToTipe env n (TDictShadow k (Left ref)) = case lookup ref env of
                                                           Nothing => Left ref
                                                           Just v => Right (TDict k v)
      shadowToTipe env n (TDictShadow k (Right v))  = case shadowToTipe env n v of
                                                           Left e => Left e
                                                           Right v' => Right (TDict k v')
      shadowToTipe env n (TArrowShadow f t)         = case shadowToTipe env n f of
                                                           Left e => Left e
                                                           Right f' => case shadowToTipe env n t of
                                                                            Left e' => Left e'
                                                                            Right t' => Right (TArrow f' t')
      shadowToTipe env n TUnitShadow                = Right TUnit
      shadowToTipe env n (TRecordShadow ps)         = let (es, ps') = liftEitherList (map (deshadowParameter env) ps) in
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
        deshadowDefType' (d@(n, t) :: xs) unsolved cnt acc = case shadowToTipe acc n t of
                                                                  Left  _  => deshadowDefType' xs (d :: unsolved) cnt acc
                                                                  Right t' => deshadowDefType' xs unsolved cnt $ insert n t' acc

    deshadowEvent : SortedMap Name Tipe -> EventShadow -> Either String Event
    deshadowEvent env (MkEventShadow n ps ms)
      = let (es, ps') = liftEitherList $ map (deshadowParameter env) ps in
            if length es > Z
               then Left (foldl (\a, x => a ++ " " ++ (bold x)) "" es)
               else Right (MkEvent n ps' ms)

    constructFsm : String -> List Parameter -> List Participant -> List Event -> List State -> List (Maybe Transition) -> Maybe (List Meta) -> Either String Fsm
    constructFsm n m ps es ss ts ms
      = do Just ps' <- liftFromMaybe $ List1.fromList ps
           | Nothing => Left ("Require one " ++ (bold "participant") ++ " at least")
           Just es' <- liftFromMaybe $ List1.fromList es
           | Nothing => Left ("Require one " ++ (bold "event") ++ " at least")
           Just ss' <- liftFromMaybe $ List1.fromList ss
           | Nothing => Left ("Require one " ++ (bold "state") ++ " at least")
           Just ts' <- liftFromMaybe $ List1.fromList $ fromMaybe [] $ liftMaybeList ts
           | Nothing => Left ("Require one " ++ (bold "transition") ++ " at least")
           pure (MkFsm n m ps' es' ss' ts' ms)
      where
        liftFromMaybe : Maybe a -> Either String (Maybe a)
        liftFromMaybe x = Right x

---------
-- API --
---------

export
analyse : SExp -> Either (ParseError SExp) (Fsm, List SExp)
analyse (SExpList sexp) = parse fsm sexp
analyse _               = Left (Error ("Expected " ++ (bold "fsm") ++ "sexp") [])
