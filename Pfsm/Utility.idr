module Pfsm.Utility

import Data.SortedSet

import Pfsm.Data

export
derefEvent : List Event -> EventRef -> Maybe Event
derefEvent []        _   = Nothing
derefEvent (x :: xs) ref = if name x == ref
                              then Just x
                              else derefEvent xs ref

export
derefState : List State -> StateRef -> Maybe State 
derefState []        _   = Nothing
derefState (x :: xs) ref = if name x == ref
                              then Just x
                              else derefState xs ref

export
liftStates : List State -> List Transition -> (SortedSet State, SortedSet State) -> (SortedSet State, SortedSet State)
liftStates states []                                     acc          = acc
liftStates states ((MkTransition src dst _ _ _ _) :: xs) (srcs, dsts) = liftStates states xs (case derefState states src of
                                                                                                   Just s => insert s srcs
                                                                                                   Nothing => srcs
                                                                                             ,case derefState states dst of
                                                                                                   Just s => insert s dsts
                                                                                                   Nothing => dsts) 

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
