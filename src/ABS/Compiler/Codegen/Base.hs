module ABS.Compiler.Codegen.Base where

import Control.Monad.Trans.Reader (Reader)
import Control.Monad.Trans.State.Strict (State)
import Data.Map (Map)

import qualified ABS.AST as ABS

type LetScope = Reader ScopeLVL

type BlockScope = State [ScopeLVL]

type ScopeLVL = Map ABS.L ABS.T