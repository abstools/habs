{-# LANGUAGE LambdaCase, ImplicitParams #-}
module Main where

import qualified ABS.AST as ABS (Program (Program))
import qualified Language.Haskell.Exts.Syntax as HS (Module (..), ModuleName (..))
import qualified Language.Haskell.Exts.Pretty as HS (prettyPrintWithMode, defaultMode, linePragmas)
import ABS.Parser

import ABS.Compiler.CmdOpt
import ABS.Compiler.Firstpass.SymbolTable
import ABS.Compiler.Codegen.Mod (tModul)

import Control.Monad (when)
import System.FilePath ((</>), pathSeparator)
import System.Directory (createDirectoryIfMissing)
import System.IO (hPrint, stderr)
import Data.List (isSuffixOf)

-- | The habs translator executable
main :: IO ()
main = do
  when (null $ abs_sources cmdOpt) $ error "No ABS files to translate are given as input. Try --help"
  
  -- 0. parse all modules to their ASTs
  modules <- concatMap (\case 
                          (absFileName,Ok (ABS.Program ms)) -> zip (repeat absFileName) ms
                          (absFileName, Bad msg) -> error (absFileName ++ " failed to parse. " ++ msg)
                       ) 
            . concat <$> mapM parseFileOrDir (abs_sources cmdOpt)
  
  -- with `--dump-ast`, sends the AST to stderr as Haskell would `show` it   
  when (dump_ast cmdOpt) $ mapM_ (hPrint stderr) modules
     
  -- 1.st-pass: build the symboltables
  let symbolTables = globalSTs (snd $ unzip modules)
     
  -- 2.nd-pass: generate code
  mapM_ (\ (absFileName, absModule) -> 
                 ppHaskellFile $ -- prettyprint the generated code as Haskell file 
                    let ?absFileName = absFileName
                    in tModul absModule symbolTables
        ) modules
  where
    -- | pretty-print a Haskell-AST to a file ".hs"
    ppHaskellFile :: HS.Module -> IO ()
    ppHaskellFile m@(HS.Module _ (HS.ModuleName s) _ _ _ _ _) = do
  
      createDirectoryIfMissing True haskellDirName -- with True, it's like mkdir -p
  
      -- prettyprint Haskell code with {-# LINE #-} pragmas between top-level decls                                             
      let hsContents = HS.prettyPrintWithMode (HS.defaultMode {HS.linePragmas = True}) m
          -- clean-up empty LINE pragmas
          hsContentsClean = unlines . filter (not . isSuffixOf "{-# LINE 1 \"<unknown>.hs\" #-}") $ lines hsContents    
      
      writeFile (haskellDirName </> haskellFileName) hsContentsClean

      where haskellFileName = map (\ c -> if c == '.' then pathSeparator else c) s  ++ ".hs"
            haskellDirName = output_dir cmdOpt
 
