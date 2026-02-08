module IntegerTest

import Hedgehog
import TTest

%hint
int1000 : Gen Integer
int1000 = integer $ constant 0 1000

test1 : (n : Integer) -> n - 1 + 1 ==> n
test1 n = MkTTest

