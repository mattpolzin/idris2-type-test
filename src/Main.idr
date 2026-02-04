module Main

import Compiler.Common

import Core.Binary
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
import Idris.IDEMode.REPL
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
import TTImp.Raw

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

import Debug.Trace

import Yaffle.Main

import TTest
import Hedgehog

%default covering

findInputs : List CLOpt -> Maybe (List1 String)
findInputs [] = Nothing
findInputs (InputFile f :: fs) =
  let rest = maybe [] toList (findInputs fs)
  in  Just (f ::: rest)
findInputs (_ :: fs) = findInputs fs

splitPaths : String -> List1 String
splitPaths = map trim . split (==pathSeparator)

-- Add extra data from the "IDRIS2_x" environment variables
updateEnv : {auto c : Ref Ctxt Defs} ->
            {auto o : Ref ROpts REPLOpts} ->
            Core ()
updateEnv
    = do defs <- get Ctxt
         noColor <- coreLift [ isJust noc || not tty | noc <- idrisGetEnv "NO_COLOR", tty <- isTTY stdout ]
         when noColor $ setColor False
         bprefix <- coreLift $ idrisGetEnv "IDRIS2_PREFIX"
         setPrefix (fromMaybe yprefix bprefix)
         bpath <- coreLift $ idrisGetEnv "IDRIS2_PATH"
         whenJust bpath $ traverseList1_ addExtraDir . splitPaths
         bdata <- coreLift $ idrisGetEnv "IDRIS2_DATA"
         whenJust bdata $ traverseList1_ addDataDir . splitPaths
         blibs <- coreLift $ idrisGetEnv "IDRIS2_LIBS"
         whenJust blibs $ traverseList1_ addLibDir . splitPaths
         pdirs <- coreLift $ idrisGetEnv "IDRIS2_PACKAGE_PATH"
         whenJust pdirs $ traverseList1_ addPackageSearchPath . splitPaths
         cg <- coreLift $ idrisGetEnv "IDRIS2_CG"
         whenJust cg $ \ e => case getCG (options defs) e of
           Just cg => setCG cg
           Nothing => throw (InternalError ("Unknown code generator " ++ show e))
         inccgs <- coreLift $ idrisGetEnv "IDRIS2_INC_CGS"
         whenJust inccgs $ \ cgs =>
           traverseList1_ (setIncrementalCG False) $
             map trim (split (==',') cgs)
         -- IDRIS2_PATH goes first so that it overrides this if there's
         -- any conflicts. In particular, that means that setting IDRIS2_PATH
         -- for the tests means they test the local version not the installed
         -- version
         defs <- get Ctxt
         -- add global package path to the package search paths (after those
         -- added by the user with IDRIS2_PACKAGE_PATH)
         addPackageSearchPath !pkgGlobalDirectory
         -- These might fail while bootstrapping
         catch (addPkgDir "prelude" anyBounds) (const (pure ()))
         catch (addPkgDir "base" anyBounds) (const (pure ()))
         addDataDir (prefix_dir (dirs (options defs)) </>
                        ("idris2-" ++ showVersion False version) </> "support")
         addLibDir (prefix_dir (dirs (options defs)) </>
                        ("idris2-" ++ showVersion False version) </> "lib")
         Just cwd <- coreLift $ currentDir
              | Nothing => throw (InternalError "Can't get current directory")
         addLibDir cwd

updateREPLOpts : {auto o : Ref ROpts REPLOpts} ->
                 Core ()
updateREPLOpts
    = do ed <- coreLift $ idrisGetEnv "EDITOR"
         whenJust ed $ \ e => update ROpts { editor := e }

tryYaffle : List CLOpt -> Core Bool
tryYaffle [] = pure False
tryYaffle (Yaffle f :: _) = do yaffleMain f []
                               pure True
tryYaffle (c :: cs) = tryYaffle cs

ignoreMissingIpkg : List CLOpt -> Bool
ignoreMissingIpkg [] = False
ignoreMissingIpkg (IgnoreMissingIPKG :: _) = True
ignoreMissingIpkg (c :: cs) = ignoreMissingIpkg cs

tryTTM : List CLOpt -> Core Bool
tryTTM [] = pure False
tryTTM (Metadata f :: _) = do dumpTTM f
                              pure True
tryTTM (c :: cs) = tryTTM cs


banner : String
banner = #"""
       ____    __     _         ___
      /  _/___/ /____(_)____   |__ \
      / // __  / ___/ / ___/   __/ /     Version \#{ showVersion True version }
    _/ // /_/ / /  / (__  )   / __/      https://www.idris-lang.org
   /___/\__,_/_/  /_/____/   /____/      Type :? for help

  Welcome to Idris 2.  Enjoy yourself!
  """#

checkVerbose : List CLOpt -> Bool
checkVerbose [] = False
checkVerbose (Verbose :: _) = True
checkVerbose (_ :: xs) = checkVerbose xs

typeOf : {vars : _} -> Term vars -> Maybe RawImp
typeOf (Ref fc nt name) = Just (IVar fc name)
typeOf (Meta fc n i ts) = Nothing
typeOf (Bind fc x b scope) = Nothing
typeOf (TType fc n) = Nothing
typeOf (Local fc isLet idx p) = Nothing
typeOf (App fc fn arg) = Nothing
typeOf (As fc side as pat) = Nothing
typeOf (TDelayed fc lz t) = Nothing
typeOf (TDelay fc lz ty arg) = Nothing
typeOf (TForce fc lz t) = Nothing
typeOf (PrimVal fc constant@(PrT _)) = Just (IPrimVal fc constant)
typeOf (PrimVal fc _) = Nothing
typeOf (Erased fc why) = Nothing

findWithin : {vars : _} -> (target : Name) -> (ty : Term vars) -> Maybe (List RawImp)
findWithin t (Ref fc nt name) = if t == name then Just [] else Nothing
findWithin t (Bind fc x (Let fc1 rig val ty) scope) = findWithin t scope
findWithin t (Bind fc x (Pi fc1 rig pinfo ty) scope) = 
  case typeOf ty of
       Just x => (x ::) <$> findWithin t scope
       Nothing => findWithin t scope
findWithin t (App fc fn arg) = findWithin t fn
findWithin _ _ = Nothing

toPaths : {root : _} -> Tree root -> IO (List String)
toPaths tree =
  depthFirst (\x => map (toFilePath x ::) . force) tree (pure [])

bindFnVar : RawImp
bindFnVar =
  let bindFnName = NS preludeNS $ UN $ Basic ">>="
  in  (IVar EmptyFC bindFnName)

mapFnVar : RawImp
mapFnVar =
  let mapFnName = NS preludeNS $ UN $ Basic "map"
  in  (IVar EmptyFC mapFnName)

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
  let gen : RawImp = ISearch EmptyFC 2
  let appGen : RawImp = apply (IVar EmptyFC forAllFnName) [gen]
  catch (checkTerm tidx InExpr [] (MkNested []) Env.empty appGen glued) $
    \e => do argTypeNames <- traverse (full context) argTypes
             coreLift $ putStrLn "Error generating arguments for \{testName}. Needed argument types: \{show argTypeNames}"
             throw e

taggedPropertyVar : RawImp
taggedPropertyVar = 
  let propertyTestNS = NS (mkNamespace "Hedgehog.Internal.Property")
      taggedPropertyName = propertyTestNS $ UN $ Basic "MkTagged"
  in  (IVar EmptyFC taggedPropertyName)

propertyCheckFnVar : RawImp
propertyCheckFnVar =
  let propertyTestRunnerNS = NS (mkNamespace "Hedgehog.Internal.Runner")
      propertyCheckFnName = propertyTestRunnerNS $ UN $ Basic "checkNamed"
  in  (IVar EmptyFC propertyCheckFnName)

propertyTestFnVar : RawImp
propertyTestFnVar =
  let propertyTestNS = NS (mkNamespace "Hedgehog.Internal.Property")
      propertyTestFnName = propertyTestNS $ UN $ Basic "property"
  in  (IVar EmptyFC propertyTestFnName)

eqPropertyFnVar : RawImp
eqPropertyFnVar =
  let ttestNS = NS (mkNamespace "TTest")
      eqPropertyFnName = ttestNS $ UN $ Basic "EqProperty"
  in  (IVar EmptyFC eqPropertyFnName)

unsafePerformIOFnVar : RawImp
unsafePerformIOFnVar =
  let unsafePerformIOName = NS primIONS (UN $ Basic "unsafePerformIO")
  in  (IVar EmptyFC unsafePerformIOName)

record TestArg where
  constructor MkTestArg
  ty : ClosedTerm
  -- ^ argument type
  gen : ClosedTerm
  -- ^ PropertyT a (generates an `a` in the PropertyT Monad)

funcX : {auto c : Ref Ctxt Defs} -> RawImp -> Scope -> List TestArg -> Core RawImp
funcX testFn scope [] = pure (apply eqPropertyFnVar [testFn])
funcX testFn scope [x] = do
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
funcX testFn scope (x :: xs) = do
  -- testFn : a -> ... -> x ==> y

  argTy <- iRawToRawImp <$> unelab Env.empty x.ty
  -- argTy : Type (a in this case)
  arg <- iRawToRawImp <$> unelab Env.empty x.gen
  -- arg : PropertyT a

  let argName = mkFresh scope (UN $ Basic "testArg")
  testFn' <- funcX testFn (argName :: scope) xs
  let lambda : RawImp = ILam EmptyFC
                             top
                             Explicit
                             (Just argName)
                             argTy
                             testFn'
  let eqProp : RawImp = apply bindFnVar [arg, lambda]
  pure eqProp

stMain : List CLOpt -> Core ()
stMain opts
    = do False <- tryYaffle opts
            | True => pure ()
         False <- tryTTM opts
            | True => pure ()
         defs <- initDefs
         c <- newRef Ctxt defs
         s <- newRef Syn initSyntax
         setCG {c} Chez
         addPrimitives

         setWorkingDir "."
         when (ignoreMissingIpkg opts) $
            setSession ({ ignoreMissingPkg := True } !getSession)

         let ide = ideMode opts
         let ideSocket = ideModeSocket opts
         let outmode = if ide then IDEMode 0 stdin stdout else REPL InfoLvl
         o <- newRef ROpts (REPL.Opts.defaultOpts Nothing outmode [])
         updateEnv
         fname <- case (findInputs opts) of
                       Just (fname ::: Nil) => pure $ Just fname
                       Nothing => pure Nothing
                       Just (fname1 ::: fnames) => do
                         let suggestion = nearMatchOptSuggestion fname1
                         renderedSuggestion <- maybe (pure "") render suggestion
                         quitWithError $
                           UserError """
                                     Expected at most one input file but was given: \{joinBy ", " (fname1 :: fnames)}
                                     \{renderedSuggestion}
                                     """
         update ROpts { mainfile := fname }

         -- start by going over the pre-options, and stop if we do not need to
         -- continue
         True <- preOptions opts
            | False => pure ()

         -- If there's a --build or --install, just do that then quit
         _ <- flip catch quitWithError $ processPackageOpts opts

         flip catch quitWithError $
            do when (checkVerbose opts) $ -- override Quiet if implicitly set
                   setOutput (REPL InfoLvl)
               u <- newRef UST initUState
               origin <- maybe
                 (pure $ Virtual Interactive) (\fname => do
                   modIdent <- ctxtPathToNS fname
                   pure (PhysicalIdrSrc modIdent)
                   ) fname
               m <- newRef MD (initMetadata origin)
               updateREPLOpts
               Just cg <- getCG Chez
                 | Nothing => coreLift $ exitWith (ExitFailure 1)
               session <- getSession
               when (not $ nobanner session) $ do
                 iputStrLn $ pretty0 banner
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

               doRepl <- catch (postOptions result opts)
                               (\err => emitError err *> pure False)

               defs <- get Ctxt
               let package = "hedgehog"
               searchDirs <- extraSearchDirectories
               let Just packageDir = find
                     (\d => isInfixOf package (fromMaybe d $ fileName =<< parent d))
                     searchDirs
                 | _ => coreLift $ exitWith (ExitFailure 1)
               let packageDirPath = parse packageDir
               tree <- coreLift $ explore packageDirPath
               fentries <- coreLift $ toPaths (toRelative tree)
               errs <- for fentries $ \entry => do
                 let entry' = dropExtensions entry
                 let sp = forget $ split (== dirSeparator) entry'
                 let ns = concat $ intersperse "." sp
                 let ns' = mkNamespace ns
                 catch (do addImport (MkImport emptyFC False (nsAsModuleIdent ns') ns'); pure Nothing)
                       (\err => pure (Just err))

               setAllPublic True
               finalDefs <- get Ctxt
               let context = finalDefs.gamma
               let ttestNS = NS (mkNamespace "TTest")
               let ttestConstructorName = ttestNS $ UN $ Basic "MkTTest"
               targetResolvedName <- resolved context (ttestNS $ UN $ Basic "==>")
               ctxt <- get Arr @{context.content}
               x <- map catMaybes $ for (rangeFromTo 0 (max ctxt)) $ \idx => do
                      Just y <- coreLift (readArray ctxt idx)
                        | Nothing => pure Nothing
                      test <- decode context idx True y
                      let False = test.fullname == ttestConstructorName
                        | True => pure Nothing
                      let ty = test.type
--                       coreLift $ printLn $ !(full context ty)
                      let Just extraArgs = (findWithin targetResolvedName ty)
                        | Nothing => pure Nothing
                      let testName = show test.fullname
--                       coreLift $ printLn extraArgs

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
                      
                      eqProp <- funcX (IVar EmptyFC test.fullname) [] testArgs
                      -- ^ PropertyT ()

--                       let propertyTestNS = NS (mkNamespace "Hedgehog.Internal.Property")
--                       let propTFn = Ref EmptyFC Func (propertyTestNS $ UN $ Basic "PropertyT")
--                       unit <- getCon EmptyFC finalDefs (builtin "Unit")
--                       let glued = gnf Env.empty (apply EmptyFC propTFn [unit])
--                       tidx <- resolveName (UN $ Basic "[elaborator script]")
--                       q <- checkTerm tidx InExpr [] (MkNested []) Env.empty eqProp glued
                      
                      let propertyTestFn : RawImp = apply propertyTestFnVar [eqProp] 
                      let taggedTestName : RawImp = apply taggedPropertyVar [IPrimVal EmptyFC (Str testName)]
                      let propertyCheckFn : RawImp = apply propertyCheckFnVar [taggedTestName, propertyTestFn] 
                      let performFn : RawImp = apply unsafePerformIOFnVar [propertyCheckFn]
--                       coreLift $ printLn performFn
                      bool <- getCon EmptyFC finalDefs (NS (preludeNS <.> (mkNamespace "Basics")) $ UN $ Basic "Bool")
                      tidx <- resolveName (UN $ Basic "[elaborator script]")
                      let glued = (gnf Env.empty bool)
                      r <- checkTerm tidx InExpr [] (MkNested []) Env.empty performFn glued
                      execute cg r
                      pure (Just test)
               pure ()

  where

  quitWithError : {auto c : Ref Ctxt Defs} ->
                {auto s : Ref Syn SyntaxInfo} ->
                {auto o : Ref ROpts REPLOpts} ->
                Error -> Core a
  quitWithError err = do
    doc <- display err
    msg <- render doc
    coreLift (die msg)

-- Run any options (such as --version or --help) which imply printing a
-- message then exiting. Returns wheter the program should continue

quitOpts : List CLOpt -> IO Bool
quitOpts [] = pure True
quitOpts (Version :: _)
    = do putStrLn versionMsg
         pure False
quitOpts (TTCVersion :: _)
    = do printLn ttcVersion
         pure False
quitOpts (Help Nothing :: _)
    = do putStrLn usage
         pure False
quitOpts (Help (Just HelpLogging) :: _)
    = do putStrLn helpTopics
         pure False
quitOpts (Help (Just HelpPragma) :: _)
    = do putStrLn pragmaTopics
         pure False
quitOpts (_ :: opts) = quitOpts opts

main : IO ()
main = do
  Right opts <- getCmdOpts
    | Left err => do ignore $ fPutStrLn stderr $ "Error: " ++ err
                     exitWith (ExitFailure 1)
  continue <- quitOpts opts
  when continue $ do
    setupTerm
    coreRun (stMain opts)
      (\err : Error => do ignore $ fPutStrLn stderr $ "Uncaught error: " ++ show err
                          exitWith (ExitFailure 1))
      (\res => pure ())
