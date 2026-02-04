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

test3 : (githubUser : String) -> compareAssignees (Just githubUser) Nothing (Just githubUser) ==> GT
test3 g = MkTTest

tmp : Property
tmp = property $
  let p = (forAll unicodeGen)
      q = (p >>= (\s => EqProperty (test3 s)))
  in q

%hint
int1000 : Gen Integer
int1000 = integer $ constant 0 1000

test1 : (n : Integer) -> n + 1 > 1 ==> True
test1 n = MkTTest

-- test2 : (the Integer 2) + 1 ==> 2
-- test2 = MkTTest
