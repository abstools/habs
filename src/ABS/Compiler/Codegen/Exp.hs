{-# LANGUAGE ImplicitParams, QuasiQuotes #-}
module ABS.Compiler.Codegen.Exp
    ( tFunBody
    , tPureExp
    )where

import ABS.Compiler.Codegen.Base
import ABS.Compiler.Utils
import ABS.Compiler.Codegen.Typ
import ABS.Compiler.Codegen.Pat
import ABS.Compiler.Firstpass.Base (SymbolTable) 
import qualified ABS.AST as ABS
import qualified Language.Haskell.Exts.Syntax as HS
import Control.Monad.Trans.Reader (runReader, local, ask)
import qualified Data.Map as M (Map, fromList, insert, member)
import Language.Haskell.Exts.SrcLoc (noLoc)
import Language.Haskell.Exts.QQ (hs)
import Data.Foldable (foldlM)

-- | Translating the body of a pure function
tFunBody :: ( ?st::SymbolTable, ?tyvars::[ABS.UIdent], ?fields :: M.Map ABS.LIdent ABS.Type, ?cname :: String) => 
           ABS.FunBody -> [ABS.Param] -> HS.Exp
tFunBody ABS.BuiltinFunBody _params = [hs| undefined |] -- builtin turned to undefined
tFunBody (ABS.NormalFunBody pexp) params = runReader (tPureExp pexp) 
                                           (M.fromList $ map (\ (ABS.Par t i) -> (i,t)) params) -- initial function scope is the formal params

-- | Translating a pure expression
tPureExp :: ( ?st::SymbolTable, ?tyvars::[ABS.UIdent], ?fields :: M.Map ABS.LIdent ABS.Type, ?cname :: String) => 
           ABS.PureExp -> ExpScope HS.Exp

tPureExp (ABS.If predE thenE elseE) = do
  tpred <- tPureExp predE
  tthen <- tPureExp thenE
  telse <- tPureExp elseE
  pure [hs| if $tpred then $tthen else $telse |]

tPureExp (ABS.Let (ABS.Par ptyp pid@(ABS.LIdent (_,var))) eqE inE) = do
  tin <- local (M.insert pid ptyp) $ tPureExp inE -- adds to scope
  teq <- tPureExp eqE
  let pat = HS.Ident var
  pure $ case ptyp of
             ABS.TUnderscore -> [hs| (\ ((pat)) -> $tin) $teq |] -- don't add type-sig, infer it
             _ -> let typ = tTypeOrTyVar ?tyvars ptyp
                 in [hs| (\ ((pat)) -> $tin) ( $teq :: ((typ)) ) |] -- maps to a haskell lambda exp

tPureExp (ABS.Case ofE branches) = do
  tof <- tPureExp ofE
  HS.Case tof <$>
    mapM (\ (ABS.CaseBranc pat pexp) -> do
            texp <- tPureExp pexp
            pure $ HS.Alt noLoc (tPattern pat) (HS.UnGuardedRhs texp) Nothing
         ) branches

tPureExp (ABS.EFunCall (ABS.LIdent (_,cid)) args) = HS.Paren <$> foldlM
                                                    (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                    (HS.Var $ HS.UnQual $ HS.Ident cid)
                                                    args
tPureExp (ABS.EQualFunCall ttyp (ABS.LIdent (_,cid)) args) = HS.Paren <$> foldlM
                                                             (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                             (HS.Var $ HS.Qual (HS.ModuleName $ showTType ttyp) $ HS.Ident cid)
                                                             args

tPureExp (ABS.ENaryFunCall (ABS.LIdent (_,cid)) args) = 
    HS.Paren . HS.App (HS.Var $ HS.UnQual $ HS.Ident cid)
          <$> HS.List <$> mapM tPureExp args

tPureExp (ABS.ENaryQualFunCall ttyp (ABS.LIdent (_,cid)) args) = do
    HS.Paren . HS.App (HS.Var $ HS.Qual (HS.ModuleName $ showTType ttyp) $ HS.Ident cid)
          <$> HS.List <$> mapM tPureExp args

-- constants
tPureExp (ABS.EEq (ABS.ELit ABS.LNull) (ABS.ELit ABS.LNull)) = pure [hs| True |]
tPureExp (ABS.EEq (ABS.ELit ABS.LThis) (ABS.ELit ABS.LThis)) = pure [hs| True |]
tPureExp (ABS.EEq (ABS.ELit ABS.LNull) (ABS.ELit ABS.LThis)) = pure [hs| False |]

-- tPureExp (ABS.EEq pnull@(ABS.ELit ABS.LNull) pvar@(ABS.EVar ident@(ABS.LIdent (p,str)))) _tyvars = do
--   tnull <- tPureExp pnull _tyvars
--   tvar <- tPureExp pvar _tyvars
--   fscope <- ask
--   case M.lookup ident fscope of -- check the type of the right var
--     Just t -> if isInterface t
--              then return $ HS.Paren $ HS.InfixApp
--                       (HS.ExpTypeSig HS.noLoc tnull (tType t))
--                        (HS.QVarOp $ HS.UnQual  $ HS.Symbol "==")
--                        (HS.ExpTypeSig HS.noLoc tvar (tType t))
--              else errorPos p "cannot equate datatype to null"
--     Nothing -> errorPos p $ str ++ " not in scope"

-- commutative
tPureExp (ABS.EEq pexp pnull@(ABS.ELit (ABS.LNull))) = tPureExp (ABS.EEq pnull pexp)

-- tPureExp (ABS.EEq pvar1@(ABS.EVar ident1@(ABS.LIdent (p1,str1))) pvar2@(ABS.EVar ident2@(ABS.LIdent (p2,str2)))) _tyvars = do
--   tvar1 <- tPureExp pvar1 _tyvars
--   tvar2 <- tPureExp pvar2 _tyvars
--   fscope <- ask
--   case M.lookup ident1 fscope of -- check the type of the right var
--     Just t1 -> case M.lookup ident2 fscope of
--                 Just t2 -> if isInterface t1 && isInterface t2
--                           then case joinSub t1 t2 of
--                               Just t ->
--                                 return $ HS.Paren $ HS.InfixApp
--                                   (HS.ExpTypeSig HS.noLoc tvar1 (tType t))
--                                   (HS.QVarOp $ HS.UnQual  $ HS.Symbol "==")
--                                   (HS.ExpTypeSig HS.noLoc tvar2 (tType t))
--                               Nothing -> error ("cannot unify the interface " ++ str1 
--                                                ++ " at position " ++ showPos p1 ++ " with interface " ++ str2 ++ " at position " ++ showPos p2)
--                           else return $ HS.Paren $ HS.InfixApp  -- treat them as both datatypes and let haskell figure out if there is a type mismatch
--                                           tvar1
--                                           (HS.QVarOp $ HS.UnQual  $ HS.Symbol "==")
--                                           tvar2
--                 Nothing -> errorPos p2 $ str2 ++ " not in scope"
--     Nothing -> errorPos p1 $ str1 ++ " not in scope"

-- a catch-all for literals,constructors maybe coupled with vars
tPureExp (ABS.EEq l r) = do tl <- tPureExp l;  tr <- tPureExp r; pure [hs| ($tl == $tr) |]

-- -- normalizess to not . ==
tPureExp (ABS.ENeq left right) = tPureExp (ABS.ELogNeg $ ABS.EEq left right) 

-- -- be careful to parenthesize infix apps
tPureExp (ABS.EOr l r)   = do tl <- tPureExp l;  tr <- tPureExp r; pure [hs| ($tl || $tr) |]
tPureExp (ABS.EAnd l r)  = do tl <- tPureExp l;  tr <- tPureExp r; pure [hs| ($tl && $tr) |]
tPureExp (ABS.ELt l r)   = do tl <- tPureExp l;  tr <- tPureExp r; pure [hs| ($tl < $tr) |]
tPureExp (ABS.ELe l r)   = do tl <- tPureExp l;  tr <- tPureExp r; pure [hs| ($tl <= $tr) |]
tPureExp (ABS.EGt l r)   = do tl <- tPureExp l;  tr <- tPureExp r; pure [hs| ($tl > $tr) |]
tPureExp (ABS.EGe l r)   = do tl <- tPureExp l;  tr <- tPureExp r; pure [hs| ($tl >= $tr) |]
tPureExp (ABS.EAdd l r)  = do tl <- tPureExp l;  tr <- tPureExp r; pure [hs| ($tl + $tr) |]
tPureExp (ABS.ESub l r)  = do tl <- tPureExp l;  tr <- tPureExp r; pure [hs| ($tl - $tr) |]
tPureExp (ABS.EMul l r)  = do tl <- tPureExp l;  tr <- tPureExp r; pure [hs| ($tl * $tr) |]
tPureExp (ABS.EDiv l r)  = do tl <- tPureExp l;  tr <- tPureExp r; pure [hs| ($tl / $tr) |]
tPureExp (ABS.EMod l r)  = do tl <- tPureExp l;  tr <- tPureExp r; pure [hs| ($tl % $tr) |]
tPureExp (ABS.ELogNeg e) = do te <- tPureExp e; pure [hs| (not $te) |]
tPureExp (ABS.EIntNeg e) = do te <- tPureExp e; pure [hs| (- $te) |]

tPureExp (ABS.ESinglConstr (ABS.QTyp [ABS.QTypeSegmen (ABS.UIdent (_,"Unit"))]))     = pure [hs| () |]
tPureExp (ABS.ESinglConstr (ABS.QTyp [ABS.QTypeSegmen (ABS.UIdent (_,"Nil"))]))      = pure [hs| [] |]
tPureExp (ABS.ESinglConstr (ABS.QTyp [ABS.QTypeSegmen (ABS.UIdent (_,"EmptyMap"))])) = pure [hs| _emptyMap |]
tPureExp (ABS.ESinglConstr (ABS.QTyp [ABS.QTypeSegmen (ABS.UIdent (_,"EmptySet"))])) = pure [hs| _emptySet |]
tPureExp (ABS.ESinglConstr qtyp) = pure $ HS.Con $ HS.UnQual $ HS.Ident $ showQType qtyp

tPureExp (ABS.EParamConstr (ABS.QTyp [ABS.QTypeSegmen (ABS.UIdent (p,"Triple"))]) pexps) =   
    if length pexps == 3
    then HS.Paren . HS.Tuple HS.Boxed <$> mapM tPureExp pexps
    else errorPos p "wrong number of arguments to Triple"
tPureExp (ABS.EParamConstr (ABS.QTyp [ABS.QTypeSegmen (ABS.UIdent (p,"Pair"))]) pexps) = 
    if length pexps == 2
    then HS.Paren . HS.Tuple HS.Boxed <$> mapM tPureExp pexps
    else errorPos p "wrong number of arguments to Pair"
tPureExp (ABS.EParamConstr (ABS.QTyp [ABS.QTypeSegmen (ABS.UIdent (_,"Cons"))]) [l, r]) = do
   tl <- tPureExp l
   tr <- tPureExp r
   pure $ [hs| ($tl : $tr) |]
tPureExp (ABS.EParamConstr (ABS.QTyp [ABS.QTypeSegmen (ABS.UIdent (p,"Cons"))]) _) = errorPos p "wrong number of arguments to Cons"
tPureExp (ABS.EParamConstr (ABS.QTyp [ABS.QTypeSegmen (ABS.UIdent (_,"InsertAssoc"))]) [l, r]) = do
  tl <- tPureExp l
  tr <- tPureExp r
  pure $ [hs| (insertAssoc $tl $tr) |]
tPureExp (ABS.EParamConstr (ABS.QTyp [ABS.QTypeSegmen (ABS.UIdent (p,"InsertAssoc"))]) _) = errorPos p "wrong number of arguments to InsertAssoc"
tPureExp (ABS.EParamConstr qtyp args) = HS.Paren <$>
    foldlM (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
    (HS.Con $ HS.UnQual $ HS.Ident $ showQType qtyp)
    args

tPureExp (ABS.EVar var@(ABS.LIdent (p,pid))) = do
     scope <- ask
     pure $ if var `M.member` scope
            then HS.Var $ HS.UnQual $ HS.Ident pid
            else if var `M.member` ?fields
                 then if null ?cname
                      then error "cannot access fields in pure context"
                      else HS.Var $ HS.UnQual $ HS.Ident $ pid ++ "'" ++ ?cname
                 else errorPos p $ pid ++ " not in scope"
                -- HS.Paren $ (if isInterface t
                --             then HS.App (HS.Var $ identI "up") -- upcasting if it is of a class type
                --             else id) 
                

-- tPureExp (ABS.EQualVar (ABS.TTyp tsegs) (ABS.LIdent (_,pid))) _tyvars = -- todo: we cannot use any scope, so we have to lookup the other modules, to check if it is of an interface type (upcast it) or int (fromIntegral) 
--     return $ HS.Var $ HS.Qual (HS.ModuleName $ joinTTypeIds tsegs) $ HS.Ident pid
--     -- we tread it as pure for now

tPureExp (ABS.EThis (ABS.LIdent (_, field))) = if null ?cname
                                               then error "cannot access fields in pure context"
                                               else let fieldFun = HS.Var $ HS.UnQual $ HS.Ident $ field ++ "'" ++ ?cname
                                                    in pure [hs| ($fieldFun this') |] -- accessor
tPureExp (ABS.ELit lit) = pure $ case lit of
                                   ABS.LStr str ->  HS.Lit $ HS.String str
                                   ABS.LInt i ->  HS.Lit $ HS.Int i
                                   ABS.LThis -> if null ?cname
                                               then error "cannot call this in pure context"
                                               else [hs| (up this) |]
                                   ABS.LNull -> [hs| (up null) |]
                                   ABS.LThisDC -> [hs| thisDC |]


