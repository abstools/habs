module ABS.Compiler.Codegen.Base where

import Control.Monad.Trans.Reader
import Data.Map (Map)

import qualified ABS.AST as ABS

type Scope = Reader (Map ABS.LIdent ABS.Type)
