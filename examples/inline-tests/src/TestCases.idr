module TestCases

import TTest
import Hedgehog
import System
import Data.String

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

%hint
int1000 : Gen Integer
int1000 = integer $ constant 0 1000

%hint
nat1000 : Gen Nat
nat1000 = nat $ constant 0 1000

good_test0 : (githubUser : String) -> compareAssignees (Just githubUser) Nothing (Just githubUser) ==> GT
good_test0 g = MkTTest

bad_test1 : (n : Integer) -> n + 1 > 1 ==> True
bad_test1 n = MkTTest

bad_test2 : (the Integer 2) + 1 ==> 2
bad_test2 = MkTTest

namespace Tests1

  bad_test3 : (x : Nat) -> (str : String) -> "\{show x}\{str}" ==> "2hi"
  bad_test3 x y = MkTTest

  good_test4 : (x : Nat)
       -> (y : Integer)
       -> (str : String)
       -> "\{show x}\{show y}\{str}" ==> (show x) ++ (show y) ++ str
  good_test4 x y str = MkTTest

good_test5 : (x : Nat) -> x + 2 > 1 ==> True
good_test5 x = MkTTest

good_test6 : String.unlines ["hi", "hello"] ==> "hi\nhello\n"
good_test6 = MkTTest

