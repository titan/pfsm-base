module Pfsm.Analyser

import public Control.Delayed
import public Text.Parser.Core
import public Text.Parser
import Pfsm.Data
import public Pfsm.Parser

------------
-- Helper --
------------

bold : String -> String
bold str = "\ESC[1m" ++ str ++ "\ESC[0m"

toMaybe : List a -> Maybe (List a)
toMaybe [] = Nothing
toMaybe xs = Just xs

--------------
-- Analyser --
--------------

Rule : Type -> Type
Rule ty = Grammar SExp True ty

EmptyRule : Type -> Type
EmptyRule ty = Grammar SExp False ty

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
    meta' : Rule Meta
    meta' = do
      k <- anyString
      v <- choose anyString meta
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
    primtype = do
      x <- prim
      pure (TPrimType x)

    list : Rule Tipe
    list = do
      string "list"
      t <- tipe
      pure (TList t)

    dict : Rule Tipe
    dict = do
      string "dict"
      p <- prim
      t <- tipe
      pure (TDict p t)

thz : Rule (Name, Tipe, Maybe (List Meta))
thz
  = terminal ("Expected " ++ (bold "the") ++ " sexp")
             (\x => case x of
                         SExpList ss => case parse thz' ss of
                                             Left _ => Nothing
                                             Right (result, _) => Just result
                         _ => Nothing)
  where
    thz' : Rule (Name, Tipe, Maybe (List Meta))
    thz' = do
      symbol "the"
      t <- tipe
      n <- anySymbol
      ms <- optional $ many meta
      pure (n, t , ms)

-----------
-- Model --
-----------

model : Rule (List (Name, Tipe, Maybe (List Meta)))
model
  = terminal ("Expected model sexp")
             (\x => case x of
                         SExpList ss => case parse model' ss of
                                             Left _ => Nothing
                                             Right (result, _) => Just result
                         _ => Nothing)
  where
    model' : Rule (List (Name, Tipe, Maybe (List Meta)))
    model' = do
      symbol "model"
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
    event' = do
      symbol "event"
      n <- anySymbol
      xs <- many thz
      pure (MkEvent n xs)

----------
-- Role --
----------

role : Rule Role
role
  = terminal ("Expected role sexp")
             (\x => case x of
                         SExpList ss => case parse role' ss of
                                             Left _ => Nothing
                                             Right (result, _) => Just result
                         _ => Nothing)
  where
    role' : Rule Role
    role' = do
      symbol "role"
      n <- anySymbol
      ms <- many meta
      pure (MkRole n ms)

----------------
-- Expression --
----------------

identifier : Rule Expression
identifier = do
  x <- anySymbol
  pure (IdentifyExpression x)

integerLiteral : Rule Expression
integerLiteral = do
  x <- integer
  pure (IntegerLiteralExpression x)

realLiteral : Rule Expression
realLiteral = do
  x <- real
  pure (RealLiteralExpression x)

stringLiteral : Rule Expression
stringLiteral = do
  x <- anyString
  pure (StringLiteralExpression x)

boolean : Rule Expression
boolean = do
  x <- (symbol "true") <|> (symbol "false")
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
      application' = do
        fun <- anySymbol
        args <- many expression
        pure (ApplicationExpression fun args)

  expression : Rule Expression
  expression
    = identifier <|> integerLiteral <|> realLiteral <|> stringLiteral <|> application <|> boolean

compare : Rule BoolExpression
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

    compare' : Rule BoolExpression
    compare' = do
      op <- operation
      lexp <- expression
      rexp <- expression
      pure (CompareExpression op lexp rexp)

primitiveBool : Rule BoolExpression
primitiveBool
  = terminal ("Expected sexp list of application or identifier or bool")
             (\x => case x of
                         SymbolAtom "true" => Just (PrimitiveBoolExpression (BooleanExpression True))
                         SymbolAtom "false" => Just (PrimitiveBoolExpression (BooleanExpression False))
                         SymbolAtom i => Just (PrimitiveBoolExpression (IdentifyExpression i))
                         SExpList ss => case parse application ss of
                                             Left _ => Nothing
                                             Right (result, _) => Just (PrimitiveBoolExpression result)
                         _ => Nothing)

mutual

  unaryBool : Rule BoolExpression
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
                                       SymbolAtom s => fromString s
                                       _ => Nothing)
  
      unaryBool' : Rule BoolExpression
      unaryBool' = do
        op <- operation
        exp <- bool
        pure (UnaryBoolExpression op exp)


  binaryBool : Rule BoolExpression
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
                                       SymbolAtom s => fromString s
                                       _ => Nothing)
  
      binaryBool' : Rule BoolExpression
      binaryBool' = do
        op <- operation
        lexp <- bool
        rexp <- bool
        pure (BinaryBoolExpression op lexp rexp)

  bool : Rule BoolExpression
  bool = unaryBool <|> binaryBool <|> compare <|> primitiveBool

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
      = do
        symbol "set!"
        i <- identifier
        e <- expression
        pure (ActionAssignment i e)
    
    return : Rule Action
    return
      = do
        symbol "return"
        i <- identifier
        pure (ActionReturn i)

    action' : Rule Action
    action' = assignment <|> return

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
    onEnter' = do
      symbol "on-enter"
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
    onExit' = do
      symbol "on-exit"
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
    unzipItems [] acc = acc
    unzipItems (x :: xs) (ens, exs, ms) = case x of
                                               Left en => unzipItems xs (en :: ens, exs, ms) 
                                               Right x1 => case x1 of
                                                                Left ex => unzipItems xs (ens, ex :: exs, ms)
                                                                Right m => unzipItems xs (ens, exs, m :: ms)
    toMaybeElem : List a -> Maybe a
    toMaybeElem [] = Nothing
    toMaybeElem (x :: xs) = Just x

    state' : Rule State
    state' = do
      symbol "state"
      n <- anySymbol
      is <- many item
      pure (MkState n
                    (toMaybeElem (fst $ unzipItems is ([], [], [])))
                    (toMaybeElem ((fst . snd) $ unzipItems is ([], [], [])))
                    (toMaybe ((snd . snd) $ unzipItems is ([], [], []))))

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
    transitionAction' = do
      symbol "action"
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
    fromTo' = do
      symbol "from-to"
      s <- anySymbol
      d <- anySymbol
      pure (s, d)

guard : Rule BoolExpression
guard
  = terminal ("Expected where sexp")
             (\x => case x of
                         SExpList ss => case parse guard' ss of
                                             Left _ => Nothing
                                             Right (result, _) => Just result
                         _ => Nothing)
  where
    guard' : Rule BoolExpression
    guard' = do
      symbol "where"
      be <- bool
      pure be


trigger : Rule (RoleRef, EventRef, Maybe BoolExpression)
trigger
  = terminal ("Expected trigger-by sexp")
             (\x => case x of
                         SExpList ss => case parse trigger' ss of
                                             Left _ => Nothing
                                             Right (result, _) => Just result
                         _ => Nothing)
  where
    trigger' : Rule (RoleRef, EventRef, Maybe BoolExpression)
    trigger' = do
      symbol "trigger-by"
      r <- anySymbol
      e <- anySymbol
      b <- optional bool
      pure (r, e, b)

transition : Rule Transition
transition
  = terminal ("Expected transition sexp")
             (\x => case x of
                         SExpList ss => case parse transition' ss of
                                             Left _ => Nothing
                                             Right (result, _) => Just result
                         _ => Nothing)
  where
    transition' : Rule Transition
    transition' = do
      symbol "transition"
      sd <- fromTo
      reg <- trigger
      as <- optional transitionAction
      let s = fst sd
      let d = snd sd
      let r = fst reg
      let e = (fst . snd) reg
      let g = (snd . snd) reg
      pure (MkTransition s d r e g as)


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

    unzipItems : List (Either Role (Either Event (Either State (Either Transition Meta)))) -> (List Role, List Event, List State, List Transition, List Meta) -> (List Role, List Event, List State, List Transition, List Meta)
    unzipItems [] acc = acc
    unzipItems (x :: xs) (rs, es, ss, ts, ms) = case x of
                                                 Left r => unzipItems xs (r :: rs, es, ss, ts, ms)
                                                 Right x1 => case x1 of
                                                                  Left e => unzipItems xs (rs, e :: es, ss, ts, ms)
                                                                  Right x2 => case x2 of
                                                                                   Left s => unzipItems xs (rs, es, s :: ss, ts, ms)
                                                                                   Right x3 => case x3 of
                                                                                                    Left t => unzipItems xs (rs, es, ss, t :: ts, ms)
                                                                                                    Right m => unzipItems xs (rs, es, ss, ts, m :: ms)

    item : Rule (Either Role (Either Event (Either State (Either Transition Meta))))
    item = do
      x <- choose role (choose event (choose state (choose transition meta)))
      pure x

    fsm' : Rule Fsm
    fsm' = do
      symbol "fsm"
      n <- anySymbol
      m <- model
      is <- many item
      pure (MkFsm n m
                  (fst $ unzipItems is ([], [], [], [], []))
                  ((fst . snd) $ unzipItems is ([], [], [], [], []))
                  ((fst . (snd . snd)) $ unzipItems is ([], [], [], [], []))
                  ((fst . (snd . (snd . snd))) $ unzipItems is ([], [], [], [], []))
                  (toMaybe ((snd . (snd . (snd . snd))) $ unzipItems is ([], [], [], [], [])))
                  )

---------
-- API --
---------

export
analyse : SExp -> Either (ParseError SExp) (Fsm, List SExp)
analyse sexp 
  = parse fsm [sexp]
