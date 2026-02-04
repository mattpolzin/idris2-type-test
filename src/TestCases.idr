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

%hint
unicodeGen : Gen String
unicodeGen = string (linear 0 30) unicode

test0 : (githubUser : String) -> compareAssignees (Just githubUser) Nothing (Just githubUser) ==> GT
test0 g = MkTTest

%hint
int1000 : Gen Integer
int1000 = integer $ constant 0 1000

test1 : (n : Integer) -> n + 1 > 1 ==> True
test1 n = MkTTest

test2 : (the Integer 2) + 1 ==> 2
test2 = MkTTest

%hint
nat1000 : Gen Nat
nat1000 = nat $ constant 0 1000

namespace Tests1

  test3 : (x : Nat) -> (str : String) -> "\{show x}\{str}" ==> "2hi"
  test3 x y = MkTTest

  test4 : (x : Nat) -> (y : Integer) -> (str : String) -> "\{show x}\{show y}\{str}" ==> (show x) ++ (show y) ++ str
  test4 x y str = MkTTest

test5 : (x : Nat) -> x + 2 > 1 ==> True
test5 x = MkTTest

