module OptionHandling

import Compiler.Common

import Idris.CommandLine
import Idris.SetOptions
import Idris.Package.Types

import Core.Context
import Core.Context.Context
import Core.Options

import System

%default total

export
ignoreMissingIpkg : List CLOpt -> Bool
ignoreMissingIpkg [] = False
ignoreMissingIpkg (IgnoreMissingIPKG :: _) = True
ignoreMissingIpkg (c :: cs) = ignoreMissingIpkg cs

checkVerbose : List CLOpt -> Bool
checkVerbose [] = False
checkVerbose (Verbose :: _) = True
checkVerbose (_ :: xs) = checkVerbose xs

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
