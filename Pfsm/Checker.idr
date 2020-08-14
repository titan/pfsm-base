module Pfsm.Checker

import Data.List
import Pfsm.Data
import Pfsm.Utility

-------------
-- Utility --
-------------

summary : List (Maybe String) -> Maybe (List String)
summary xs
  = summary' xs []
  where
    summary' : List (Maybe String) -> List String -> Maybe (List String)
    summary' []        []  = Nothing
    summary' []        acc = Just acc
    summary' (x :: xs) acc = case x of
                                  Just x' => summary' xs (x' :: acc)
                                  Nothing => summary' xs acc

-----------
-- Event --
-----------

checkEventRef : EventRef -> List Event -> Maybe String
checkEventRef er []        = Just ("Undefined event " ++ er)
checkEventRef er (x :: xs) = if x.name == er
                                then Nothing
                                else checkEventRef er xs
-----------------
-- Participant --
-----------------

checkParticipantRef : ParticipantRef -> List Participant -> Maybe String
checkParticipantRef pr []        = Just ("Undefined participant " ++ pr)
checkParticipantRef pr (x :: xs) = if x.name == pr
                                      then Nothing
                                      else checkParticipantRef pr xs

-----------
-- State --
-----------

checkStateRef : StateRef -> List State -> Maybe String
checkStateRef sr []        = Just ("Undefined state " ++ sr)
checkStateRef sr (x :: xs) = if x.name == sr
                                then Nothing
                                else checkStateRef sr xs

---------
-- API --
---------

checkParticipants : Fsm -> List (Maybe String)
checkParticipants fsm
  = flatten $ map (\x => map (\y => checkParticipantRef y.participant fsm.participants) x.triggers) fsm.transitions

checkEvents : Fsm -> List (Maybe String)
checkEvents fsm
  = flatten $ map (\x => map (\y => checkEventRef y.event fsm.events) x.triggers) fsm.transitions

checkSrcStates : Fsm -> List (Maybe String)
checkSrcStates fsm
  = map (\x => checkStateRef x.src fsm.states) fsm.transitions

checkDstStates : Fsm -> List (Maybe String)
checkDstStates fsm
  = map (\x => checkStateRef x.dst fsm.states) fsm.transitions

export
defaultCheckingRules : List (Fsm -> List (Maybe String))
defaultCheckingRules
  = [checkParticipants, checkEvents, checkSrcStates, checkDstStates]

export
check : Fsm -> List (Fsm -> List (Maybe String)) -> Maybe (List String)
check fsm rules
  = summary $ foldr (\y, a => y ++ a) [] $ map (\x => x fsm) rules
