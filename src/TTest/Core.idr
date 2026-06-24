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

export
tTestTypeName : Name
tTestTypeName =
  let ttestNS = NS (mkNamespace "TTest")
  in  ttestNS $ UN $ Basic "==>"

export
tTestConstructorName : Name
tTestConstructorName =
  let ttestNS = NS (mkNamespace "TTest")
  in  ttestNS $ UN $ Basic "MkTTest"

export
argsInPropM : {auto c : Ref Ctxt Defs} ->
              {auto m : Ref MD Metadata} ->
              {auto u : Ref UST UState} ->
              {auto s : Ref Syn SyntaxInfo} ->
              {auto o : Ref ROpts REPLOpts} ->
              Context ->
              (testName : String) ->
              List ClosedTerm ->
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

export
propFn : {auto c : Ref Ctxt Defs} -> RawImp -> Scope -> List TestArg -> Core RawImp
propFn testFn scope [] = pure (apply eqPropertyFnVar [testFn])
propFn testFn scope [x] = do
  -- testFn : a -> x ==> y

  argTy <- iRawToRawImp <$> unelab Env.empty x.ty
  -- argTy : Type (a in this case)
  arg <- iRawToRawImp <$> unelab Env.empty x.gen
  -- arg : PropertyT a

  let ivarOf : Name -> RawImp = IVar EmptyFC

  let argName = mkFresh scope (UN $ Basic "testArg")
  let lambda : RawImp = ILam EmptyFC 
                             top
                             Explicit
                             (Just argName)
                             argTy 
                             (apply eqPropertyFnVar [apply testFn (ivarOf <$> reverse (argName :: scope))])
  let eqProp : RawImp = apply bindFnVar [arg, lambda]
  pure eqProp

propFn testFn scope (x :: xs) = do
  -- testFn : a -> ... -> x ==> y

  argTy <- iRawToRawImp <$> unelab Env.empty x.ty
  -- argTy : Type (a in this case)
  arg <- iRawToRawImp <$> unelab Env.empty x.gen
  -- arg : PropertyT a

  let argName = mkFresh scope (UN $ Basic "testArg")
  testFn' <- propFn testFn (argName :: scope) xs
  let lambda : RawImp = ILam EmptyFC
                             top
                             Explicit
                             (Just argName)
                             argTy
                             testFn'
  let eqProp : RawImp = apply bindFnVar [arg, lambda]
  pure eqProp

