{-# LANGUAGE ImplicitParams, QuasiQuotes #-}
module ABS.Compiler.Codegen.StmExp
    ( tStmExp
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

-- | Translating a pure expression

tStmExp :: ( ?st::SymbolTable, ?vars::M.Map ABS.LIdent ABS.Type, ?fields :: M.Map ABS.LIdent ABS.Type, ?cname :: String) => 
          ABS.PureExp -> ExpScope HS.Exp
tStmExp (ABS.If predE thenE elseE) = do
  tpred <- tStmExp predE
  tthen <- tStmExp thenE
  telse <- tStmExp elseE
  pure $ HS.Do [ HS.Generator noLoc (HS.PVar $ HS.Ident "if'") tpred
               , HS.Qualifier [hs| if if' then $tthen else $telse |]
               ]

tStmExp (ABS.Let (ABS.Par ptyp pid@(ABS.LIdent (_,var))) eqE inE) = do
  tin <- local (M.insert pid ptyp) $ tStmExp inE -- adds to scope
  teq <- tStmExp eqE
  let pat = HS.Ident var
  pure $ case ptyp of
             ABS.TUnderscore -> [hs| (\ ((pat)) -> $tin) =<< $teq |] -- don't add type-sig, infer it
             _ -> let typ = tType ptyp
                 in [hs| (\ ((pat)) -> $tin) =<< ( $teq :: ((typ)) ) |] -- maps to a haskell lambda exp

tStmExp (ABS.Case ofE branches) = do
  tof <- tStmExp ofE
  tcase <- HS.Case (HS.Var $ HS.UnQual $ HS.Ident "of'") <$>
          mapM (\ (ABS.CaseBranc pat pexp) -> do
                  texp <- tStmExp pexp
                  pure $ HS.Alt noLoc (tPattern pat) (HS.UnGuardedRhs texp) Nothing
               ) branches
  pure $ HS.Do [ HS.Generator noLoc (HS.PVar $ HS.Ident "of'") tof
               , HS.Qualifier tcase
               ]

tStmExp (ABS.EFunCall (ABS.LIdent (_,cid)) args) = foldlM
                                                    (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs| $acc <*> $targ |])
                                                    [hs| I'.pure $(HS.Var $ HS.UnQual $ HS.Ident cid) |]
                                                    args
tStmExp (ABS.EQualFunCall ttyp (ABS.LIdent (_,cid)) args) = foldlM
                                                             (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs| $acc <*> $targ |])
                                                             [hs| I'.pure $(HS.Var $ HS.Qual (HS.ModuleName $ showTType ttyp) $ HS.Ident cid) |]
                                                             args

tStmExp (ABS.ENaryFunCall (ABS.LIdent (_,cid)) args) = do
    targs <- HS.List <$> mapM tStmExp args
    pure [hs| $(HS.Var $ HS.UnQual $ HS.Ident cid) (sequence $targs) |]


tStmExp (ABS.ENaryQualFunCall ttyp (ABS.LIdent (_,cid)) args) = do
    targs <- HS.List <$> mapM tStmExp args
    pure [hs| $(HS.Var $ HS.Qual (HS.ModuleName $ showTType ttyp) $ HS.Ident cid) (sequence $targs) |]

-- constants
tStmExp (ABS.EEq (ABS.ELit ABS.LNull) (ABS.ELit ABS.LNull)) = pure [hs| I'.pure True |]
tStmExp (ABS.EEq (ABS.ELit ABS.LThis) (ABS.ELit ABS.LThis)) = pure [hs| I'.pure True |]
tStmExp (ABS.EEq (ABS.ELit ABS.LNull) (ABS.ELit ABS.LThis)) = pure [hs| I'.pure False |]

-- tStmExp (ABS.EEq pnull@(ABS.ELit ABS.LNull) pvar@(ABS.EVar ident@(ABS.LIdent (p,str)))) _tyvars = do
--   tnull <- tStmExp pnull _tyvars
--   tvar <- tStmExp pvar _tyvars
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
tStmExp (ABS.EEq pexp pnull@(ABS.ELit (ABS.LNull))) = tStmExp (ABS.EEq pnull pexp)

-- tStmExp (ABS.EEq pvar1@(ABS.EVar ident1@(ABS.LIdent (p1,str1))) pvar2@(ABS.EVar ident2@(ABS.LIdent (p2,str2)))) _tyvars = do
--   tvar1 <- tStmExp pvar1 _tyvars
--   tvar2 <- tStmExp pvar2 _tyvars
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
tStmExp (ABS.EEq l r) = do tl <- tStmExp l;  tr <- tStmExp r; pure [hs| (==) <$> $tl <*> $tr |]

-- -- normalizess to not . ==
tStmExp (ABS.ENeq left right) = tStmExp (ABS.ELogNeg $ ABS.EEq left right) 

-- -- be careful to parenthesize infix apps
tStmExp (ABS.EOr l r)   = do tl <- tStmExp l;  tr <- tStmExp r; pure [hs| (||) <$> $tl <*> $tr |]
tStmExp (ABS.EAnd l r)  = do tl <- tStmExp l;  tr <- tStmExp r; pure [hs| (^) <$> $tl <*> $tr |]
tStmExp (ABS.ELt l r)   = do tl <- tStmExp l;  tr <- tStmExp r; pure [hs| (<) <$> $tl <*> $tr |]
tStmExp (ABS.ELe l r)   = do tl <- tStmExp l;  tr <- tStmExp r; pure [hs| (<=) <$> $tl <*> $tr |]
tStmExp (ABS.EGt l r)   = do tl <- tStmExp l;  tr <- tStmExp r; pure [hs| (>) <$> $tl <*> $tr |]
tStmExp (ABS.EGe l r)   = do tl <- tStmExp l;  tr <- tStmExp r; pure [hs| (>=) <$> $tl <*> $tr |]
tStmExp (ABS.EAdd l r)  = do tl <- tStmExp l;  tr <- tStmExp r; pure [hs| (+) <$> $tl <*> $tr |]
tStmExp (ABS.ESub l r)  = do tl <- tStmExp l;  tr <- tStmExp r; pure [hs| (-) <$> $tl <*> $tr |]
tStmExp (ABS.EMul l r)  = do tl <- tStmExp l;  tr <- tStmExp r; pure [hs| (*) <$> $tl <*> $tr |]
tStmExp (ABS.EDiv l r)  = do tl <- tStmExp l;  tr <- tStmExp r; pure [hs| (/) <$> $tl <*> $tr |]
tStmExp (ABS.EMod l r)  = do tl <- tStmExp l;  tr <- tStmExp r; pure [hs| (%) <$> $tl <*> $tr |]
tStmExp (ABS.ELogNeg e) = do te <- tStmExp e; pure [hs| (not) <$> $te |]
tStmExp (ABS.EIntNeg e) = do te <- tStmExp e; pure [hs| (-) <$> $te |]

tStmExp (ABS.ESinglConstr (ABS.QTyp [ABS.QTypeSegmen (ABS.UIdent (_,"Unit"))]))     = pure [hs| I'.pure () |]
tStmExp (ABS.ESinglConstr (ABS.QTyp [ABS.QTypeSegmen (ABS.UIdent (_,"Nil"))]))      = pure [hs| I'.pure [] |]
tStmExp (ABS.ESinglConstr (ABS.QTyp [ABS.QTypeSegmen (ABS.UIdent (_,"EmptyMap"))])) = pure [hs| I'.pure _emptyMap |]
tStmExp (ABS.ESinglConstr (ABS.QTyp [ABS.QTypeSegmen (ABS.UIdent (_,"EmptySet"))])) = pure [hs| I'.pure _emptySet |]
tStmExp (ABS.ESinglConstr qtyp) = pure [hs| I'.pure $(HS.Con $ HS.UnQual $ HS.Ident $ showQType qtyp) |]

tStmExp (ABS.EParamConstr (ABS.QTyp [ABS.QTypeSegmen (ABS.UIdent (p,"Triple"))]) pexps) =   
    if length pexps == 3
    then do
      let [pexp1,pexp2,pexp3] = pexps
      texp1 <- tStmExp pexp1
      texp2 <- tStmExp pexp2
      texp3 <- tStmExp pexp3
      pure [hs| (,,) <$> $texp1 <*> $texp2 <*> $texp3 |]
    else errorPos p "wrong number of arguments to Triple"
tStmExp (ABS.EParamConstr (ABS.QTyp [ABS.QTypeSegmen (ABS.UIdent (p,"Pair"))]) pexps) = 
    if length pexps == 2
    then do
      let [pexp1,pexp2] = pexps
      texp1 <- tStmExp pexp1
      texp2 <- tStmExp pexp2
      pure [hs| (,) <$> $texp1 <*> $texp2 |]
    else errorPos p "wrong number of arguments to Pair"
tStmExp (ABS.EParamConstr (ABS.QTyp [ABS.QTypeSegmen (ABS.UIdent (_,"Cons"))]) [l, r]) = do
   tl <- tStmExp l
   tr <- tStmExp r
   pure $ [hs| (:) <$> $tl <*> $tr |]
tStmExp (ABS.EParamConstr (ABS.QTyp [ABS.QTypeSegmen (ABS.UIdent (p,"Cons"))]) _) = errorPos p "wrong number of arguments to Cons"
tStmExp (ABS.EParamConstr (ABS.QTyp [ABS.QTypeSegmen (ABS.UIdent (_,"InsertAssoc"))]) [l, r]) = do
  tl <- tStmExp l
  tr <- tStmExp r
  pure $ [hs| insertAssoc <$> $tl <*> $tr |]
tStmExp (ABS.EParamConstr (ABS.QTyp [ABS.QTypeSegmen (ABS.UIdent (p,"InsertAssoc"))]) _) = errorPos p "wrong number of arguments to InsertAssoc"
tStmExp (ABS.EParamConstr qtyp args) = 
    foldlM
    (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs| $acc <*> $targ |])
    [hs| I'.pure $(HS.Con $ HS.UnQual $ HS.Ident $ showQType qtyp) |]
    args

tStmExp (ABS.EVar var@(ABS.LIdent (p,pid))) = do
     scope <- ask
     pure $ if var `M.member` scope
            then [hs| I'.pure $(HS.Var $ HS.UnQual $ HS.Ident pid) |]
            else if var `M.member` ?vars
                 then [hs| I'.readIORef $(HS.Var $ HS.UnQual $ HS.Ident pid) |]
                 else if var `M.member` ?fields
                      then if null ?cname
                           then errorPos p "cannot access fields here"
                           else let fieldFun = HS.Var $ HS.UnQual $ HS.Ident $ pid ++ "'" ++ ?cname
                                in [hs| I'.pure ($fieldFun this') |] -- accessor
                 else errorPos p $ pid ++ " not in scope"
                -- HS.Paren $ (if isInterface t
                --             then HS.App (HS.Var $ identI "up") -- upcasting if it is of a class type
                --             else id) 
                

-- tStmExp (ABS.EQualVar (ABS.TTyp tsegs) (ABS.LIdent (_,pid))) _tyvars = -- todo: we cannot use any scope, so we have to lookup the other modules, to check if it is of an interface type (upcast it) or int (fromIntegral) 
--     return $ HS.Var $ HS.Qual (HS.ModuleName $ joinTTypeIds tsegs) $ HS.Ident pid
--     -- we tread it as pure for now

tStmExp (ABS.EThis (ABS.LIdent (_, field))) = if null ?cname
                                               then error "cannot access fields in pure context"
                                               else pure $ let fieldFun = HS.Var $ HS.UnQual $ HS.Ident $ field ++ "'" ++ ?cname
                                                           in [hs| I'.pure ($fieldFun this') |] -- accessor
tStmExp (ABS.ELit lit) = pure $ case lit of
                                   ABS.LStr str ->  [hs| I'.pure $(HS.Lit $ HS.String str) |]
                                   ABS.LInt i ->  [hs| I'.pure $(HS.Lit $ HS.Int i) |]
                                   ABS.LThis -> if null ?cname
                                               then error "cannot call this here"
                                               else [hs| I'.pure (up this) |]
                                   ABS.LNull -> [hs| I'.pure (up null) |]
                                   ABS.LThisDC -> [hs| I'.pure thisDC |]


