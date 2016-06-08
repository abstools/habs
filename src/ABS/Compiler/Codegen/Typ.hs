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
tTypeOrTyVar :: [ABS.U]     -- ^ tyvars in scope
             -> ABS.T         -- ^ abs type
             -> HS.Type
tTypeOrTyVar _ (ABS.TSimple (ABS.U_ (ABS.U (_, "Exception")))) = HS.TyCon $ HS.Qual (HS.ModuleName "I'") (HS.Ident "SomeException")
tTypeOrTyVar tyvars (ABS.TSimple qtyp)  = 
       let (q, cname) = splitQU qtyp    
       in if ABS.U (undefined, cname) `elem` tyvars -- type variable
          then HS.TyVar $ HS.Ident $ headToLower cname
          else HS.TyCon $ (if null q
                           then HS.UnQual 
                           else HS.Qual (HS.ModuleName q)) (HS.Ident cname)
tTypeOrTyVar tyvars (ABS.TPoly qtyp tyargs) = foldl (\ tyacc tynext -> HS.TyApp tyacc (tTypeOrTyVar tyvars tynext)) (tType (ABS.TSimple qtyp)) tyargs
tTypeOrTyVar _tyvars ABS.TInfer = todo undefined

tType :: ABS.T -> HS.Type
tType = tTypeOrTyVar []
