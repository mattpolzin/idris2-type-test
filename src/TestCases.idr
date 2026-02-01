module TestCases

import TTest
import Hedgehog
import System

compareAssignees : (githubUser : Maybe String) -> (assignee1 : Maybe String) -> (assignee2 : Maybe String) -> Ordering
compareAssignees Nothing _ _ = EQ
compareAssignees _ Nothing Nothing = EQ
compareAssignees (Just u) Nothing (Just a2) =
  if u == a2 then GT else LT
compareAssignees (Just u) (Just a1) Nothing =
  if u == a1 then LT else GT
compareAssignees (Just u) (Just a1) (Just a2) =
  if a1 == a2
     then EQ
     else if u == a2
             then GT
             else if u == a1
                     then LT
                     else EQ

test3 : (githubUser : String) -> compareAssignees (Just githubUser) Nothing (Just githubUser) ==> GT
test3 g = MkTTest

test1 : (the Integer 1) + 1 ==> 2
test1 = MkTTest

test2 : (the Integer 2) + 1 ==> 2
test2 = MkTTest
