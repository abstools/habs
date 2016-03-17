module ABS.Compiler.Codegen.Typ
    ( tTypeOrTyVar
    , tType
    ) where

import qualified ABS.AST as ABS
import qualified Language.Haskell.Exts.Syntax as HS


tTypeOrTyVar :: [ABS.UIdent]     -- ^ tyvars in scope
             -> ABS.Type         -- ^ abs type
             -> HS.Type
tTypeOrTyVar = undefined

tType :: ABS.Type -> HS.Type
tType = tTypeOrTyVar []
