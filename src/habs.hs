module Main where

import ABS.Compiler.CmdOpt
import Control.Exception (evaluate)

-- | main
main :: IO ()
main = do
  _ <- evaluate cmdOpt           -- force the cmdopt parsing, otherwise will not run even --help
  return ()
