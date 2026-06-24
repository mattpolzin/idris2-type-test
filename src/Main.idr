module Main

import Compiler.Common

import Core.Core
import Core.Directory
import Core.InitPrimitives
import Core.Metadata
import Core.UnifyState
import Core.Normalise.Eval
import Core.Reflect
import Core.Env
import Core.TT

import Idris.CommandLine
import Idris.Env
import Idris.Package
import Idris.ProcessIdr
import Idris.REPL
import Idris.SetOptions
import Idris.Syntax
import Idris.Version
import Idris.Pretty
import Idris.Error
import Idris.Doc.Display

import TTImp.TTImp
import TTImp.Elab
import TTImp.Elab.Check
import TTImp.Unelab

import IdrisPaths
import System
import System.Directory
import System.File.Meta
import System.File.Virtual
import Libraries.Utils.Path
import Libraries.System.Directory.Tree
import System.Term

import Data.IOArray
import Data.String
import Data.List

import TTest
import TTest.Core
import TTest.Locate
import Hedgehog
import TTImp.Vars
import TTImp.Raw
import OptionHandling

%default covering

findInputs : List CLOpt -> List String
findInputs [] = []
findInputs (InputFile f :: fs) = f :: findInputs fs
findInputs (_ :: fs) = findInputs fs

stMain : List CLOpt -> Core ()
stMain opts
    = do defs <- initDefs
         c <- newRef Ctxt defs
         s <- newRef Syn initSyntax
         setCG {c} Chez
         addPrimitives

         setWorkingDir "."
         when (ignoreMissingIpkg opts) $
            setSession ({ ignoreMissingPkg := True } !getSession)

         let outmode = REPL InfoLvl
         o <- newRef ROpts (REPL.Opts.defaultOpts Nothing outmode [])
         updateEnv
         let fnames = findInputs opts

         for_ fnames $ \fname => do
           let fname = Just fname
           update ROpts { mainfile := fname }

           s <- newRef PostS defaultPost

           Continue <- handleOpts opts
              | Abort => pure ()

           Continue <- flip catch quitWithError $ processPackageOpts opts
              | Abort => pure ()

           flip catch quitWithError $
              do u <- newRef UST initUState
                 origin <- maybe
                   (pure $ Virtual Interactive) (\fname => do
                     modIdent <- ctxtPathToNS fname
                     pure (PhysicalIdrSrc modIdent)
                     ) fname
                 m <- newRef MD (initMetadata origin)
                 session <- getSession
                 fname <- if findipkg session
                             then findIpkg fname
                             else pure fname
                 setMainFile fname
                 result <- case fname of
                      Nothing => logTime 1 "Loading prelude" $ do
                                   when (not $ noprelude session) $
                                     readPrelude True
                                   pure Done
                      Just f => logTime 1 "Loading main file" $ do
                                  res <- loadMainFile f
                                  displayStartupErrors res
                                  pure res

                 post <- get PostS
                 Continue <- catch (postOptions result post)
                                 (\err => emitError err *> pure Abort)
                  | Abort => do
                      -- exit with an error code if there was an error, otherwise
                      -- just exit
                       ropts <- get ROpts
                       showTimeRecord
                       whenJust (errorLine ropts) $ \ _ =>
                         coreLift $ exitWith (ExitFailure 1)

                 setAllPublic True
                 finalDefs <- get Ctxt
                 let context = finalDefs.gamma
                 targetResolvedName <- resolved context tTestTypeName
                 ctxt <- get Arr @{context.content}
                 for_ (rangeFromTo 0 (max ctxt)) $ \idx => do
                    Just y <- coreLift (readArray ctxt idx)
                      | Nothing => pure ()
                    test <- decode context idx True y
                    let False = test.fullname == tTestConstructorName
                      | True => pure ()
                    let ty = test.type
                    let Just extraArgs = (findWithin targetResolvedName ty)
                      | Nothing => pure ()
                    let testName = show test.fullname

                    argTypes : List ClosedTerm <- for extraArgs $ \arg => do
                      tidx <- resolveName (UN $ Basic "[elaborator script]")
                      let glued = gnf Env.empty (TType EmptyFC (UN $ Basic "Type"))
                      catch (checkTerm tidx InExpr [] (MkNested []) Env.empty arg glued) $
                        \e => do coreLift $ putStrLn "Error while determining argument types for \{testName}"
                                 throw e
                    
                    argsInProp <- argsInPropM context testName argTypes
                    -- ^ now we've got List (PropertyT a) for list of arguments
                    let testArgs = zipWith MkTestArg argTypes argsInProp 
                    -- ^ zip arg generators and their generated types
                    
                    eqProp <- propFn (IVar EmptyFC test.fullname) [] testArgs
                    -- ^ PropertyT ()
                    
                    let propertyTestFn : RawImp = apply propertyTestFnVar [eqProp] 
                    let taggedTestName : RawImp = apply taggedPropertyVar [IPrimVal EmptyFC (Str testName)]
                    let propertyCheckFn : RawImp = apply propertyCheckFnVar [taggedTestName, propertyTestFn] 
                    let performFn : RawImp = apply unsafePerformIOFnVar [propertyCheckFn]
                    bool <- getCon EmptyFC finalDefs (NS (preludeNS <.> (mkNamespace "Basics")) $ UN $ Basic "Bool")
                    tidx <- resolveName (UN $ Basic "[elaborator script]")
                    let glued = (gnf Env.empty bool)
                    r <- checkTerm tidx InExpr [] (MkNested []) Env.empty performFn glued
                    Just cg <- findCG
                      | Nothing => coreLift $ exitWith (ExitFailure 1)
                    execute cg r

  where

  quitWithError : {auto c : Ref Ctxt Defs} ->
                {auto s : Ref Syn SyntaxInfo} ->
                {auto o : Ref ROpts REPLOpts} ->
                Error -> Core a
  quitWithError err = do
    doc <- display err
    msg <- render doc
    coreLift (die msg)

-- There are three ways to run the compiler
-- Either run normally, or run in yaffle mode, or dump TTM
data Entrypoint
  = Normal (List CLOpt)
  | Yaffle String
  | TTM String

parameters (allOpts : List CLOpt)

  -- Yaffle and TTM are mutually incompatible so we parse the flags here and
  -- report the error if it occurs. If neither flag is present we run in normal mode

  parseCompilerMode' : List CLOpt -> Maybe Entrypoint -> Either String Entrypoint
  parseCompilerMode' [] Nothing = pure $ Normal allOpts
  parseCompilerMode' [] (Just m) = pure m
  parseCompilerMode' (Yaffle f :: xs) Nothing = parseCompilerMode' xs (Just $ Yaffle f)
  parseCompilerMode' (Metadata f :: xs) Nothing = parseCompilerMode' xs (Just $ TTM f)
  parseCompilerMode' (Yaffle _ :: xs) (Just (TTM _)) = Left "Incompatible modes --ttm and --yaffle"
  parseCompilerMode' (Metadata _ :: xs) (Just (Yaffle _)) = Left "Incompatible modes --ttm and --yaffle"
  parseCompilerMode' (_ :: xs) m = parseCompilerMode' xs m

  parseCompilerMode : Either String Entrypoint
  parseCompilerMode = parseCompilerMode' allOpts Nothing

allMain : Entrypoint -> Core ()
allMain (Normal opts) = stMain opts
allMain (Yaffle f) = pure ()
allMain (TTM f) = pure ()

main : IO ()
main = do
  Right opts <- getCmdOpts
    | Left err => do ignore $ fPutStrLn stderr $ "Error: " ++ err
                     exitWith (ExitFailure 1)
  
  setupTerm
  let Right cliMode = parseCompilerMode opts
    | Left err => do ignore $ fPutStrLn stderr $ "Error: " ++ err
                     exitWith (ExitFailure 1)
  coreRun (allMain cliMode)
    (\err : Error => do ignore $ fPutStrLn stderr $ "Uncaught error: " ++ show err
                        exitWith (ExitFailure 1))
    (\res => pure ())
