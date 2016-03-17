{-# LANGUAGE ImplicitParams, QuasiQuotes #-}
module ABS.Compiler.Codegen.Stm
    ( tMethod
    , tBlock
    ) where

import ABS.Compiler.Codegen.Base
import ABS.Compiler.Firstpass.Base (SymbolTable)
import qualified ABS.AST as ABS
import qualified Language.Haskell.Exts.Syntax as HS
import Control.Monad.Trans.Reader (runReader)
import qualified Data.Map as M (Map, fromList, union)

tMethod :: (?st :: SymbolTable) => 
          ABS.Block                 -- the method pody
        -> [ABS.Param]               -- the method params
        -> M.Map ABS.LIdent ABS.Type -- the fields
        -> HS.Exp

tMethod b params fields = runReader (tBlock b) 
                          -- initial method scope is the UNION of formal params AND fields
                          (M.fromList (map (\ (ABS.Par t i) -> (i,t)) params) `M.union` fields)

tBlock :: (?st :: SymbolTable) => 
         ABS.Block -> Scope HS.Exp

tBlock = undefined


