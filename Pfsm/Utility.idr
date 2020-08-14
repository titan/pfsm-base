module Pfsm.Utility

import Data.List
import Data.SortedSet
import Data.Strings
import Data.Vect

import Pfsm.Data

export
repeat : String -> Nat -> String
repeat str cnt
  = repeat' "" str cnt
  where
    repeat' : String -> String -> Nat -> String
    repeat' acc _   0   = acc
    repeat' acc str cnt = repeat' (acc ++ str) str (minus cnt 1)

namespace Data.Strings
  export
  capital : String -> String
  capital str
    = case strUncons str of
           Nothing => str
           Just (c, r) => strCons (toUpper c) r

  export
  camelize : String -> String
  camelize s = foldl (\acc, x => acc ++ capital x) "" (split (== '-') s)

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
      index' a [] _        = Nothing
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

export
derefEvent : EventRef -> List Event -> Maybe Event
derefEvent _   []        = Nothing
derefEvent ref (x :: xs) = if name x == ref
                              then Just x
                              else derefEvent ref xs

export
derefState : StateRef -> List State -> Maybe State
derefState _   []        = Nothing
derefState ref (x :: xs) = if name x == ref
                              then Just x
                              else derefState ref xs

liftStates : List State -> List Transition -> (SortedSet State, SortedSet State) -> (SortedSet State, SortedSet State)
liftStates ss []                              acc          = acc
liftStates ss ((MkTransition sr dr _ ) :: xs) (srcs, dsts) = liftStates ss xs ( case derefState sr ss of
                                                                                     Just s => insert s srcs
                                                                                     Nothing => srcs
                                                                              , case derefState dr ss of
                                                                                     Just s => insert s dsts
                                                                                     Nothing => dsts
                                                                              )

export
startState : Fsm -> Maybe State
startState fsm
  = let ss = (Data.SortedSet.toList . fst) $ liftStates (states fsm) (transitions fsm) (empty, empty) in
        case ss of
             [] => Nothing
             (x :: xs) => Just x

export
stopState : Fsm -> SortedSet State
stopState fsm
  = snd $ liftStates (states fsm) (transitions fsm) (empty, empty)
