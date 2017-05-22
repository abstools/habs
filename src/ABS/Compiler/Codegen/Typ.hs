{-# LANGUAGE CPP, QuasiQuotes, ImplicitParams, LambdaCase #-}
module ABS.Compiler.Codegen.Typ
    ( tTypeOrTyVar
    , tType
    , unifyMany, instantiateMany, instantiateOne
    , buildInfo, buildUp
    ) where

import ABS.Compiler.Utils


import qualified ABS.AST as ABS
import ABS.Compiler.Firstpass.Base
import Language.Haskell.Exts.QQ (hs)
import qualified Data.Map as M
import qualified Language.Haskell.Exts.Syntax as HS
import Data.List (find)


import Control.Exception (assert)
#define todo assert False (error "not implemented yet")
#define total assert False (error "This error should not happen. Contact developers")

-- | Translating an ABS type or an ABS type-variable to a Haskell type
tTypeOrTyVar :: [ABS.U]     -- ^ tyvars in scope
             -> ABS.T       -- ^ abs type
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

instantiateOne :: M.Map String ABS.T -> ABS.T -> ABS.T
instantiateOne bs tyvar@(ABS.TSimple (ABS.U_ (ABS.U (_,s)))) = case M.lookup s bs of
                                                                Nothing -> tyvar
                                                                Just t' -> t'
instantiateOne bs (ABS.TPoly qu ts) = ABS.TPoly qu $ map (instantiateOne bs) ts 
instantiateOne _ t = t

instantiateMany :: M.Map String ABS.T -> [ABS.T] -> [ABS.T]
instantiateMany bs = foldr (\ v acc -> instantiateOne bs v : acc) []
-- instantiateMany bs = foldr (\case
--                               ABS.TSimple (ABS.U_ (ABS.U (_,s))) -> case M.lookup s bs of
--                                                                       Nothing -> id
--                                                                       Just t -> (t:) 
--                               _ -> id) []


unifyMany :: (?st::SymbolTable) 
          => [ABS.U] 
          -> [ABS.T] 
          -> [ABS.T] 
          -> M.Map String ABS.T
unifyMany tyvars args1 args2 = foldl (flip ($)) (M.fromList $ map (\ (ABS.U (_,tyvarName)) -> (tyvarName,ABS.TInfer)) tyvars) $ zipWith unify args1 args2
  where
    unify :: (?st :: SymbolTable)
          => ABS.T 
          -> ABS.T
          -> M.Map String ABS.T 
          -> M.Map String ABS.T
    -- 1. Any type variable unifies with any type expression, and is instantiated to that expression. A specific theory might restrict this rule with an occurs check.
    unify (ABS.TSimple (ABS.U_ mtyvar1@(ABS.U (_, mtyvar1String)))) ty2 bs 
      | mtyvar1 `elem` tyvars = M.insertWith mostGeneral mtyvar1String ty2 bs
      | otherwise = bs -- ignore concrete types
    unify (ABS.TSimple _) _ bs = bs --ignore concrete types
    unify (ABS.TPoly _ _) ABS.TInfer bs = bs
    unify (ABS.TPoly _qu1 ts1) (ABS.TPoly _qu2 ts2) bs =
      -- assume _qu1 == _qu2, haskell will check that anyway
      foldl (flip ($)) bs $ zipWith unify ts1 ts2
    unify t1@(ABS.TPoly _ _) t2@(ABS.TSimple _) _ = error $ "cannot unify " ++ show t1 ++ " to " ++  show t2
    unify ABS.TInfer _ _ = todo -- unification over type inference can only work for ADTS, interface types

    mostGeneral :: (?st :: SymbolTable) => ABS.T -> ABS.T -> ABS.T
    mostGeneral ABS.TInfer ty2 = ty2
    mostGeneral ty1 ABS.TInfer = ty1
    mostGeneral (ABS.TSimple (ABS.U_ (ABS.U (_,"Int")))) y@(ABS.TSimple (ABS.U_ (ABS.U (_,"Rat")))) = y
    mostGeneral x@(ABS.TSimple (ABS.U_ (ABS.U (_,"Rat")))) (ABS.TSimple (ABS.U_ (ABS.U (_,"Int")))) = x
    mostGeneral ty1@(ABS.TSimple (ABS.U_ (ABS.U (_,s1)))) ty2@(ABS.TSimple (ABS.U_ (ABS.U (_,s2)))) = 
      case (M.lookup (SN s1 Nothing) ?st, M.lookup (SN s2 Nothing) ?st)  of
          (Just (SV (Interface _ es1) _), Just (SV (Interface _ es2) _)) -> if (SN s2 Nothing) `elem` (SN s1 Nothing):M.keys es1 -- also checks for type equality
                                                                            then ty2
                                                                            else if (SN s1 Nothing) `elem` M.keys es2
                                                                                 then ty1
                                                                                 else error "not unifiable interfaces"
          _ -> ty1 -- error
    mostGeneral (ABS.TPoly c ts1)  (ABS.TPoly _ ts2)= ABS.TPoly c (zipWith mostGeneral ts1 ts2) 
    mostGeneral _ _ = error "no mostGeneral"



-- Used for subtyping

data Info = Up
          | Deep String Int [(Int,Info)]

buildInfo :: (?st :: SymbolTable) => ABS.T -> ABS.T -> Maybe Info
buildInfo _ ABS.TInfer = Nothing
buildInfo (ABS.TSimple (ABS.U_ u1)) t@(ABS.TSimple (ABS.U_ u2)) 
  | u1 == u2 = Nothing
  | otherwise = if isInterface t
                then Just Up
                else Nothing
buildInfo _ t@(ABS.TSimple _) = if isInterface t
                                then Just Up
                                else Nothing

buildInfo (ABS.TPoly (ABS.U_ (ABS.U (_,"Fut"))) _) (ABS.TPoly (ABS.U_ (ABS.U (_,"Fut"))) _) = Nothing -- TODO: Fut<A> should be covariant, but for implementation reasons (MVar a) it is invariant
buildInfo (ABS.TPoly _ ts1) (ABS.TPoly qu ts2) = let (l, buildArgs) = foldl (\ (i,acc) (t1,t2) -> maybe (i+1,acc) (\x -> (i+1,(i,x):acc)) (buildInfo t1 t2) ) (0,[]) (zip ts1 ts2)
                              in if null buildArgs
                                 then Nothing
                                 else Just $ Deep (showQU qu) l buildArgs
buildInfo _ _ = total

isInterface :: (?st::SymbolTable) => ABS.T -> Bool
isInterface ABS.TInfer = False
isInterface (ABS.TSimple (ABS.U_ (ABS.U (_,"Rat")))) = True
isInterface (ABS.TSimple (ABS.U_ (ABS.U (_,"Int")))) = True
isInterface t = let
                  qtyp = case t of
                           ABS.TSimple qtyp' -> qtyp'
                           ABS.TPoly qtyp' _ -> qtyp'
                           _ -> error "this cannot pattern match"
                  (prefix, ident) = splitQU qtyp
                  mSymbolType = if null prefix
                                then snd <$> find (\ (SN ident' modul,_) -> ident == ident' && maybe True (not . snd) modul) (M.assocs ?st)
                                else M.lookup (SN ident (Just (prefix, True))) ?st 
                in case mSymbolType of
                     Just (SV (Interface _ _) _) -> True
                     _ -> False



buildUp :: Info -> HS.Exp
buildUp Up = [hs|up'|]
buildUp (Deep functorName functorWidth deeps) = foldl 
                                              (\ acc i -> HS.App acc $ maybe [hs|I'.id|] (HS.Paren . buildUp) (lookup i deeps))
                                              (HS.Var $ HS.UnQual $ HS.Ident $ "fmap'" ++ functorName)
                                              [0..functorWidth-1]



-- (\ unified actual exp -> -- todo: optimize if unified == actual, don't up
--                         maybe exp (\ info -> HS.ExpTypeSig noLoc'(HS.App (buildUp info) exp) (tType unified)) (buildInfo unified))

