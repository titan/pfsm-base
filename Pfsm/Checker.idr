module Pfsm.Checker

import Data.List
import Pfsm.Data

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
----------
-- Role --
----------

checkRoleRef : RoleRef -> List Role -> Maybe String
checkRoleRef rr []        = Just ("Undefined role " ++ rr)
checkRoleRef rr (x :: xs) = if x.name == rr
                               then Nothing
                               else checkRoleRef rr xs

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

export
check : Fsm -> Maybe (List String)
check fsm
  = summary $ foldr (\y, a => y ++ a) [] $ map (\x => x fsm) rules
  where
    checkRoles : Fsm -> List (Maybe String)
    checkRoles fsm = map (\x => checkRoleRef x.triggerBy fsm.roles) fsm.transitions

    checkEvents : Fsm -> List (Maybe String)
    checkEvents fsm = map (\x => checkEventRef x.event fsm.events) fsm.transitions

    checkSrcStates : Fsm -> List (Maybe String)
    checkSrcStates fsm = map (\x => checkStateRef x.src fsm.states) fsm.transitions

    checkDstStates : Fsm -> List (Maybe String)
    checkDstStates fsm = map (\x => checkStateRef x.dst fsm.states) fsm.transitions

    rules : List (Fsm -> List (Maybe String))
    rules = [checkRoles, checkEvents, checkSrcStates, checkDstStates]
