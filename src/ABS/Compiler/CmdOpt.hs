{-# LANGUAGE DeriveDataTypeable #-}
-- | Possible options passed to The ABS-Haskell compiler
module ABS.Compiler.CmdOpt where

import System.Console.CmdArgs
import System.IO.Unsafe (unsafePerformIO)

{-# NOINLINE cmdOpt #-}
cmdOpt :: CmdOpt
cmdOpt = unsafePerformIO (cmdArgs cmdOptSpec)

data CmdOpt = CmdOpt {
      src_files :: [FilePath]     -- ^ The input ABS module files (ending in .abs) or ABS directories
    , output_dir :: Maybe FilePath -- ^ In which directory to put all the Haskell translated files (.hs files)
    , create_script :: Bool -- ^ creates a helper bash script for easier invoking the ghc Haskell compiler and puts it in the outputdir
    , dump_ast :: Bool            -- ^ A flag to dump the parsed AST to stderr
    } deriving (Show, Data)

cmdOptSpec :: CmdOpt
cmdOptSpec = CmdOpt { 
               src_files = def &= args &= typ "FILES/DIRS"
             , output_dir = def &= typDir &= help "In which directory to put all the Haskell translated files (.hs files)" 
             , create_script = def &= help "If given, creates a helper bash script for easier invoking the ghc Haskell compiler."
             , dump_ast = def &= help "A flag to dump the parsed AST to stderr"
             }
             &= program "habs" 
             &= help "A transcompiler from the ABS language to Haskell. Expects as input the ABS module files (ending in .abs) or whole directories containing ABS code." 
             &= helpArg [explicit, name "h", name "help"]
             &= summary ("The ABS-Haskell compiler, Nikolaos Bezirgiannis, Envisage Project") -- summary is --version

