module ABS.Compiler.Firstpass.Base where

import Data.Map (Map)

type ModuleName = String

-- | A mapping of 'Module's to their 'SymbolTable's
type SymbolTables = Map ModuleName SymbolTable

-- | A separate SymbolTable for each module
type SymbolTable = Map SymbolName SymbolValue

-- | Name of the Symbol, coupled with its origin, and if it is qualified-imported
data SymbolName = SN 
                  String        -- unqualified name
                  (Maybe (ModuleName, IsQualified)) -- where it comes from? is it qualified imported?
                  deriving (Eq, Ord, Show)          -- needed for having it as Map's index

-- | The entry of the Symbol, its symbol type and if it is exported
data SymbolValue = SV SymbolType IsExported
                 deriving Show

-- | The different symbol types
data SymbolType = Function
                | Datatype
                | Datacons String -- ^ from which datatype it comes (required by Haskell module system)
                | Exception
                | Class
                | Interface [(String,[String])] (Map SymbolName [(String,[String])]) -- ^ its direct method names, http-callable formal parameters & map of *all* extends interfaces to their own methods, http-callable formal parameters
                | Foreign
                  deriving Show

type IsQualified = Bool
type IsExported = Bool

