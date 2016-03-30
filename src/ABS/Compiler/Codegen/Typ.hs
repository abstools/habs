{-# LANGUAGE CPP #-}
module ABS.Compiler.Codegen.Typ
    ( tTypeOrTyVar
    , tType
    ) where

import ABS.Compiler.Utils

import qualified ABS.AST as ABS
import qualified Language.Haskell.Exts.Syntax as HS

import Control.Exception (assert)
#define todo assert False

-- | Translating an ABS type or an ABS type-variable to a Haskell type
tTypeOrTyVar :: [ABS.UIdent]     -- ^ tyvars in scope
             -> ABS.Type         -- ^ abs type
             -> HS.Type
tTypeOrTyVar tyvars (ABS.TSimple qtyp)  = 
       let (q, cname) = splitQType qtyp    
       in if ABS.UIdent (undefined, cname) `elem` tyvars -- type variable
          then HS.TyVar $ HS.Ident $ headToLower cname
          else HS.TyCon $ (if null q
                           then HS.UnQual 
                           else HS.Qual (HS.ModuleName q)) (HS.Ident cname)
tTypeOrTyVar tyvars (ABS.TGen qtyp tyargs) = foldl (\ tyacc tynext -> HS.TyApp tyacc (tTypeOrTyVar tyvars tynext)) (tType (ABS.TSimple qtyp)) tyargs
tTypeOrTyVar tyvars _ = todo undefined

tType :: ABS.Type -> HS.Type
tType = tTypeOrTyVar []
