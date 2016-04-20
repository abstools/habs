{-# LANGUAGE CPP, LambdaCase #-}
module Main where

import qualified ABS.AST as ABS (Program (Prog))
import qualified Language.Haskell.Exts.Syntax as HS (Module (..), ModuleName (..))
import qualified Language.Haskell.Exts.Pretty as HS (prettyPrint)
import ABS.Parser

import ABS.Compiler.CmdOpt
import ABS.Compiler.Firstpass.SymbolTable
import ABS.Compiler.Codegen.Mod (tModul)

import Control.Monad (when)
import System.FilePath ((</>))
import System.Directory (createDirectoryIfMissing)
import System.IO (hPrint, stderr)

#if __GLASGOW_HASKELL__ < 710
import Control.Applicative (pure, (<$>), (<*>))
#endif

-- | The habs translator executable
main :: IO ()
main = 
  if null (src_files cmdOpt)
  then error "No ABS files to translate are given as input. Try --help"
  else do
     -- 0. parse all modules to their ASTs
     modules <- concatMap (\case (_,Ok (ABS.Prog ms)) -> ms
                                 (fileName, Bad msg) -> error $ fileName ++ " failed to parse. " ++ msg) 
                                 . concat <$> mapM parseFileOrDir (src_files cmdOpt)
     when (dump_ast cmdOpt) $ mapM_ (hPrint stderr) modules
     -- 1.st-pass: build the symboltables
     let symbolTables = globalSTs modules
     -- 2.nd-pass: generate code
     mapM_ (\ m -> ppHaskellFile $ tModul m symbolTables)  modules

-- | pretty-print a Haskell-AST to a file ".hs"
ppHaskellFile :: HS.Module -> IO ()
ppHaskellFile m@(HS.Module _ (HS.ModuleName s) _ _ _ _ _) = do
  let haskellFileName = map (\ c -> if c == '.' then '/' else c) s  ++ ".hs"
  let haskellDirName = output_dir cmdOpt
  createDirectoryIfMissing True haskellDirName -- with True, it's like mkdir -p
  writeFile (haskellDirName </> haskellFileName) $ HS.prettyPrint m

