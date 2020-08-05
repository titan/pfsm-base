module Pfsm.Utility

import Data.SortedSet

import Pfsm.Data

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
liftStates ss []                                   acc          = acc
liftStates ss ((MkTransition sr dr _ _ _ _) :: xs) (srcs, dsts) = liftStates ss xs ( case derefState sr ss of
                                                                                          Just s => insert s srcs
                                                                                          Nothing => srcs
                                                                                   , case derefState dr ss of
                                                                                          Just s => insert s dsts
                                                                                          Nothing => dsts
                                                                                   )

export
startState : Fsm -> Maybe State
startState fsm
  = let ss = (toList . fst) $ liftStates (states fsm) (transitions fsm) (empty, empty) in
        case ss of
             [] => Nothing
             (x :: xs) => Just x

export
stopState : Fsm -> SortedSet State
stopState fsm
  = snd $ liftStates (states fsm) (transitions fsm) (empty, empty)
