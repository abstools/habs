module ABS.Compiler.Codegen.Base where

import Control.Monad.Trans.Reader (Reader)
import Control.Monad.Trans.State.Strict (State)
import Data.Map (Map)

import qualified ABS.AST as ABS

type ExpScope = Reader (Map ABS.LIdent ABS.Type)

type StmScope = State [Map ABS.LIdent ABS.Type]
