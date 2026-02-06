module TTImp.Vars

import TTImp.TTImp
import Core.Name
import Core.FC

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
  let propertyTestNS = NS (mkNamespace "Hedgehog.Internal.Property")
      taggedPropertyName = propertyTestNS $ UN $ Basic "MkTagged"
  in  (IVar EmptyFC taggedPropertyName)

export
propertyCheckFnVar : RawImp
propertyCheckFnVar =
  let propertyTestRunnerNS = NS (mkNamespace "Hedgehog.Internal.Runner")
      propertyCheckFnName = propertyTestRunnerNS $ UN $ Basic "checkNamed"
  in  (IVar EmptyFC propertyCheckFnName)

export
propertyTestFnVar : RawImp
propertyTestFnVar =
  let propertyTestNS = NS (mkNamespace "Hedgehog.Internal.Property")
      propertyTestFnName = propertyTestNS $ UN $ Basic "property"
  in  (IVar EmptyFC propertyTestFnName)

export
eqPropertyFnVar : RawImp
eqPropertyFnVar =
  let ttestNS = NS (mkNamespace "TTest")
      eqPropertyFnName = ttestNS $ UN $ Basic "EqProperty"
  in  (IVar EmptyFC eqPropertyFnName)

export
unsafePerformIOFnVar : RawImp
unsafePerformIOFnVar =
  let unsafePerformIOName = NS primIONS (UN $ Basic "unsafePerformIO")
  in  (IVar EmptyFC unsafePerformIOName)
