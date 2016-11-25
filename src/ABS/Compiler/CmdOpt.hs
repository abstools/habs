{-# LANGUAGE DeriveDataTypeable #-}
-- | Possible options passed to The ABS-Haskell compiler
module ABS.Compiler.CmdOpt where

import System.Console.CmdArgs
import System.IO.Unsafe (unsafePerformIO)

{-# NOINLINE cmdOpt #-}
cmdOpt :: CmdOpt
cmdOpt = unsafePerformIO (cmdArgs cmdOptSpec)

data CmdOpt = CmdOpt {
      abs_sources :: [FilePath]     -- ^ The input ABS module files (ending in .abs) or ABS directories
    , output_dir :: FilePath -- ^ In which directory to put all the Haskell translated files (.hs files)
    , create_script :: Bool -- ^ creates a helper bash script for easier invoking the ghc Haskell compiler and puts it in the outputdir
    , dump_ast :: Bool            -- ^ A flag to dump the parsed AST to stderr
    , nostdlib :: Bool
    } deriving (Show, Data, Typeable)

cmdOptSpec :: CmdOpt
cmdOptSpec = CmdOpt { 
               abs_sources = def &= args &= typ "FILES/DIRS"
             , output_dir = "gen/haskell" &= typDir &= help "In which directory to put all the Haskell translated files (.hs files)" 
             , create_script = def &= help "If given, creates a helper bash script for easier invoking the ghc Haskell compiler."
             , dump_ast = def &= help "A flag to dump the parsed AST to stderr"
             , nostdlib = def &= help "Will not include by-default the ABS.StdLib module. You have to do it manually with an import declaration."
             }
             &= program "habs" 
             &= help "A transcompiler from the ABS language to Haskell. Expects as input the ABS module files (ending in .abs) or whole directories containing ABS code." 
             &= helpArg [explicit, name "h", name "help"]
             &= summary ("The ABS-Haskell compiler, Nikolaos Bezirgiannis, Envisage Project") -- summary is --version

