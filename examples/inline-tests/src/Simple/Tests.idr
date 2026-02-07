module Simple.Tests

import Simple

import Data.String
import Hedgehog
import TTest

%hint
unicodeGen : Gen String
unicodeGen = string (linear 0 30) unicode

%hint
int1000 : Gen Integer
int1000 = integer $ constant 0 1000

operationTest1 : (str : String) -> (i : Integer) -> head' (words (operation str i)) ==> Just str
operationTest1 str i = MkTTest

