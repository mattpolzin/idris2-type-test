module TTest.Core

import Core.Context
import Core.Env
import Core.Metadata
import Core.Name
import Core.UnifyState

import Idris.Syntax
import Idris.REPL

import TTImp.TTImp
import TTImp.Elab
import TTImp.Elab.Check
import TTImp.Unelab

-- from this project:
import TTImp.Raw
import TTImp.Vars

tTestNS : Name -> Name
tTestNS = NS (mkNamespace "TTest")

export
tTestTypeName : Name
tTestTypeName = tTestNS $ UN $ Basic "==>"

export
tTestConstructorName : Name
tTestConstructorName = tTestNS $ UN $ Basic "MkTTest"

||| Take a list of argument types (types of arguments to the property being
||| tested) and turn it into a list of expressions of those types under
||| PropertyT by using Gens (generators) located by searching the context.
|||
||| In the TTest `(x : String) -> x ==> x`, the arg types will be (as closed
||| terms) `[String]` and the return of this function will be of type
||| `[PropertyT String]`
export
argsInPropM : {auto c : Ref Ctxt Defs} ->
              {auto m : Ref MD Metadata} ->
              {auto u : Ref UST UState} ->
              {auto s : Ref Syn SyntaxInfo} ->
              {auto o : Ref ROpts REPLOpts} ->
              Context ->
              (testName : String) ->
              (argTypes : List ClosedTerm) ->
              Core (List ClosedTerm)
argsInPropM context testName argTypes = for argTypes $ \argTy => do
  let propertyTestNS = NS (mkNamespace "Hedgehog.Internal.Property")
  let forAllFnName = propertyTestNS $ UN $ Basic "forAll"
  tidx <- resolveName (UN $ Basic "[elaborator script]")
  let propTFn = Ref EmptyFC Func (propertyTestNS $ UN $ Basic "PropertyT")
  let glued = gnf Env.empty (apply EmptyFC propTFn [argTy])
  let gen : RawImp = ISearch EmptyFC 100
  let appGen : RawImp = apply (IVar EmptyFC forAllFnName) [gen]
  catch (checkTerm tidx InExpr [] (MkNested []) Env.empty appGen glued) $
    \e => do argTypeNames <- traverse (full context) argTypes
             coreLift $ putStrLn "Error generating arguments for \{testName}. Needed argument types: \{show argTypeNames}"
             throw e

public export
record TestArg where
  constructor MkTestArg
  ty : ClosedTerm
  -- ^ argument type
  gen : ClosedTerm
  -- ^ PropertyT a (generates an `a` in the PropertyT Monad)

||| Takes an unapplied test function and list of arguments and folds the test
||| function into a PropertyT by generating each argument in the PropertyT
||| monad. You get back both the PropertyT and a PropertyConfig.
export
propFn : {auto c : Ref Ctxt Defs} -> (testFn : RawImp) -> Scope -> List TestArg -> Core RawImp
propFn testFn scope [] = pure (apply eqPropertyFnVar [testFn])
propFn testFn scope (x :: xs) = do
  argTy <- iRawToRawImp <$> unelab Env.empty x.ty
  -- argTy : Type (a in this case)
  arg <- iRawToRawImp <$> unelab Env.empty x.gen
  -- arg : PropertyT a

  let argName = mkFresh scope (UN $ Basic "testArg")

  go argTy arg argName xs

  where
    lambdaFn : (argTy : RawImp) -> (argName : Name) -> (testFn' : RawImp) -> RawImp
    lambdaFn argTy argName testFn' =
      ILam EmptyFC 
           top
           Explicit
           (Just argName)
           argTy 
           testFn'

    eqProp : (arg : RawImp) -> (lambda : RawImp) -> RawImp
    eqProp arg lambda = apply bindFnVar [arg, lambda]

    go : (argTy : RawImp) -> (arg : RawImp) -> (argName : Name) -> (additionalArgs : List TestArg) -> Core RawImp
    go argTy arg argName [] = do
      -- testFn : a -> x ==> y

      testFn' <- propFn (apply testFn (IVar EmptyFC <$> reverse (argName :: scope))) [] []
      let lambda  = lambdaFn argTy argName testFn'

      pure $ eqProp arg lambda

    go argTy arg argName xs = do
      -- testFn : a -> ... -> x ==> y

      testFn' <- propFn testFn (argName :: scope) xs
      let lambda = lambdaFn argTy argName testFn'

      pure $ eqProp arg lambda

||| Like PropFn but gives back a Property instead of a PropertyT ()
|||
||| For tests that have no inputs, creates a property that runs 1 test
||| iteration. For tests with at least one input, creates a property that runs
||| 100 test iterations.
export
prop :  {auto c : Ref Ctxt Defs} -> (testFn : RawImp) -> Scope -> List TestArg -> Core RawImp
prop testFn scope [] = do
  prop <- propFn testFn scope []
  pure $ apply property1TestFnVar [prop]
prop testFn scope args = do
  prop <- propFn testFn scope args 
  pure $ apply propertyTestFnVar [prop]

