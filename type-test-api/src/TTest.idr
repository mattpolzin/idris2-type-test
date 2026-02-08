module TTest

import Hedgehog
import System

export infixl 0 ==>

public export
record (==>) (source : a) (target : a) where
  constructor MkTTest
  {auto eqPrf : Eq a}
  {auto showPrf : Show a}

public export
EqProperty : {x,y : _} -> x ==> y -> PropertyT ()
EqProperty (MkTTest @{eqPrf} @{showPrf}) = x === y

