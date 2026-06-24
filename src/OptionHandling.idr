module OptionHandling

import Compiler.Common

import Core.Context
import Core.Context.Context
import Core.Directory
import Core.Options

import Data.String
import Data.List1

import IdrisPaths

import Idris.CommandLine
import Idris.Env
import Idris.Package.Types
import Idris.REPL
import Idris.SetOptions
import Idris.Version

import Libraries.Data.Version
import Libraries.Utils.Path

import System
import System.Directory
import System.File.Meta
import System.File.Virtual

%default total

splitPaths : String -> List1 String
splitPaths = map trim . split (==pathSeparator)

-- Add extra data from the "IDRIS2_x" environment variables
export
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

export
ignoreMissingIpkg : List CLOpt -> Bool
ignoreMissingIpkg [] = False
ignoreMissingIpkg (IgnoreMissingIPKG :: _) = True
ignoreMissingIpkg (c :: cs) = ignoreMissingIpkg cs

export
handleOpts : {auto c : Ref Ctxt Defs} ->
             {auto s : Ref PostS PostSession} ->
             List CLOpt ->
             Core ControlFlow
handleOpts (SetCG e :: opts)
    = do defs <- get Ctxt
         case getCG (options defs) e of
            Just cg => do setCG cg
                          handleOpts opts
            Nothing =>
              do coreLift $ putStrLn "No such code generator"
                 coreLift $ putStrLn $ "Code generators available: " ++
                                 showSep ", " (map fst (availableCGs (options defs)))
                 coreLift $ exitWith (ExitFailure 1)
handleOpts (PkgPath p :: opts)
    = do addPkgDir p anyBounds
         handleOpts opts
handleOpts (SourceDir d :: opts)
    = do setSourceDir (Just d)
         handleOpts opts
handleOpts (FindIPKG :: opts)
    = do setSession ({ findipkg := True } !getSession)
         handleOpts opts
handleOpts _ = pure Continue
