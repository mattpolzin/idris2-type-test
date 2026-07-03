module TTImp.Vars

import TTImp.TTImp
import Core.Name
import Core.FC

tTestNS : Name -> Name
tTestNS = NS (mkNamespace "TTest")

propertyTestNS : Name -> Name
propertyTestNS = NS (mkNamespace "Hedgehog.Internal.Property")

export
bindFnVar : RawImp
bindFnVar =
  let bindFnName = NS preludeNS $ UN $ Basic ">>="
  in  (IVar EmptyFC bindFnName)

export
mapFnVar : RawImp
mapFnVar =
  let mapFnName = NS preludeNS $ UN $ Basic "map"
  in  (IVar EmptyFC mapFnName)

export
taggedPropertyVar : RawImp
taggedPropertyVar = 
  let taggedPropertyName = propertyTestNS $ UN $ Basic "MkTagged"
  in  (IVar EmptyFC taggedPropertyName)

export
propertyCheckFnVar : RawImp
propertyCheckFnVar =
  let propertyTestRunnerNS = NS (mkNamespace "Hedgehog.Internal.Runner")
      propertyCheckFnName = propertyTestRunnerNS $ UN $ Basic "checkNamed"
  in  (IVar EmptyFC propertyCheckFnName)

||| property : PropertyT () -> Property
export
propertyTestFnVar : RawImp
propertyTestFnVar =
  let propertyTestFnName = propertyTestNS $ UN $ Basic "property"
  in  (IVar EmptyFC propertyTestFnName)

||| property1 : PropertyT () -> Property
export
property1TestFnVar : RawImp
property1TestFnVar =
  let propertyTestFnName = propertyTestNS $ UN $ Basic "property1"
  in  (IVar EmptyFC propertyTestFnName)

export
eqPropertyFnVar : RawImp
eqPropertyFnVar =
  let eqPropertyFnName = tTestNS $ UN $ Basic "EqProperty"
  in  (IVar EmptyFC eqPropertyFnName)

export
unsafePerformIOFnVar : RawImp
unsafePerformIOFnVar =
  let unsafePerformIOName = NS primIONS (UN $ Basic "unsafePerformIO")
  in  (IVar EmptyFC unsafePerformIOName)
