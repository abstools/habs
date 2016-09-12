{-# LANGUAGE ImplicitParams, QuasiQuotes #-}
module ABS.Compiler.Codegen.Exp
    ( tFunBody
    , tPureExp
    )where

import ABS.Compiler.Codegen.Base
import ABS.Compiler.Utils
import ABS.Compiler.Codegen.Typ
import ABS.Compiler.Codegen.Pat
import ABS.Compiler.Firstpass.Base
import qualified ABS.AST as ABS
import qualified Language.Haskell.Exts.Syntax as HS
import Control.Monad.Trans.Reader (runReader, local, ask)
import qualified Data.Map as M (fromList, insert, lookup, union, assocs)
import Language.Haskell.Exts.QQ (hs)
import Data.Foldable (foldlM)
import Data.List (find)

-- | Translating the body of a pure function
tFunBody :: (?st::SymbolTable, ?tyvars::[ABS.U], ?fields::ScopeLVL, ?cname::String)
         => ABS.FunBody -> [ABS.FormalPar] -> HS.Exp
tFunBody ABS.BuiltinFunBody _params = [hs|(I'.error "builtin called")|] -- builtin turned to undefined
tFunBody (ABS.NormalFunBody pexp) params = runReader (tPureExp pexp) 
                                           (M.fromList $ map (\ (ABS.FormalPar t i) -> (i,t)) params) -- initial function scope is the formal params

-- | Translating a pure expression
tPureExp :: ( ?st::SymbolTable, ?tyvars::[ABS.U], ?fields::ScopeLVL, ?cname::String) 
         => ABS.PureExp -> LetScope HS.Exp

tPureExp (ABS.EIf predE thenE elseE) = do
  tpred <- tPureExp predE
  tthen <- tPureExp thenE
  telse <- tPureExp elseE
  pure [hs|if $tpred then $tthen else $telse|]

tPureExp (ABS.ELet (ABS.FormalPar ptyp pid@(ABS.L (_,var))) eqE inE) = do
  tin <- local (M.insert pid ptyp) $ tPureExp inE -- adds to scope
  teq <- tPureExp eqE
  let pat = HS.Ident var
  pure $ case ptyp of
             ABS.TInfer -> [hs|(\ ((pat)) -> $tin) $teq|] -- don't add type-sig, infer it
             _ -> let typ = tTypeOrTyVar ?tyvars ptyp
                 in [hs|(\ ((pat)) -> $tin) ( $teq :: ((typ)) )|] -- maps to a haskell lambda exp

tPureExp (ABS.ECase ofE branches) = do
  tof <- tPureExp ofE
  HS.Case tof <$>
    mapM (\ (ABS.ECaseBranch pat pexp) -> do
            texp <- tPureExp pexp
            (tpat,tguards) <- tPattern pat
            pure $ HS.Alt noLoc' tpat ((if null tguards then HS.UnGuardedRhs else (HS.GuardedRhss . pure . HS.GuardedRhs noLoc' tguards)) texp) Nothing
         ) branches

tPureExp (ABS.EFunCall ql args) = HS.Paren <$> foldlM
                                                    (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                    (HS.Var $ HS.UnQual $ HS.Ident $ showQL ql)
                                                    args

tPureExp (ABS.ENaryFunCall ql args) = 
    HS.Paren . HS.App (HS.Var $ HS.UnQual $ HS.Ident $ showQL ql) . HS.List <$> mapM tPureExp args


-- constants
tPureExp (ABS.EEq (ABS.ELit ABS.LNull) (ABS.ELit ABS.LNull)) = pure [hs|True|]
tPureExp (ABS.EEq (ABS.ELit ABS.LThis) (ABS.ELit ABS.LThis)) = pure [hs|True|]
tPureExp (ABS.EEq (ABS.ELit ABS.LNull) (ABS.ELit ABS.LThis)) = pure [hs|False|]

-- optimization, to wrap null with the direct interface of rhs instead of up'
tPureExp (ABS.EEq (ABS.ELit ABS.LNull) pvar@(ABS.EVar ident@(ABS.L (p,str)))) = do
   scope <- ask
   tvar <- tPureExp pvar
   pure $ case M.lookup ident (scope `M.union` ?fields) of -- check the type of the right var
            Just (ABS.TSimple qu) -> [hs|( $(HS.Var $ HS.UnQual $ HS.Ident $ showQU qu) null == $tvar )|]
            Just _ -> errorPos p "cannot equate null to non-interface type"
            Nothing -> errorPos p $ str ++ " variable not in scope or has foreign type"
-- commutative
tPureExp (ABS.EEq pvar@(ABS.EVar _) pnull@(ABS.ELit ABS.LNull)) = tPureExp (ABS.EEq pnull pvar)

-- optimization, to wrap null with the direct interface of rhs instead of up'
tPureExp (ABS.EEq (ABS.ELit ABS.LNull) pvar@(ABS.EField ident@(ABS.L (p,str)))) = do
   tvar <- tPureExp pvar
   pure $ case M.lookup ident ?fields of -- check the type of the right var
            Just (ABS.TSimple qu) -> [hs|( $(HS.Var $ HS.UnQual $ HS.Ident $ showQU qu) null == $tvar )|]
            Just _ -> errorPos p "cannot equate null to non-interface type"
            Nothing -> errorPos p $ str ++ " not in scope"
-- commutative
tPureExp (ABS.EEq pvar@(ABS.EField _) pnull@(ABS.ELit ABS.LNull)) = tPureExp (ABS.EEq pnull pvar)

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
--                                   (HS.ExpTypeSig HS.noLoc' tvar1 (tType t))
--                                   (HS.QVarOp $ HS.UnQual  $ HS.Symbol "==")
--                                   (HS.ExpTypeSig HS.noLoc' tvar2 (tType t))
--                               Nothing -> error ("cannot unify the interface " ++ str1 
--                                                ++ " at position " ++ showPos p1 ++ " with interface " ++ str2 ++ " at position " ++ showPos p2)
--                           else return $ HS.Paren $ HS.InfixApp  -- treat them as both datatypes and let haskell figure out if there is a type mismatch
--                                           tvar1
--                                           (HS.QVarOp $ HS.UnQual  $ HS.Symbol "==")
--                                           tvar2
--                 Nothing -> errorPos p2 $ str2 ++ " not in scope"
--     Nothing -> errorPos p1 $ str1 ++ " not in scope"

-- a catch-all for literals,constructors maybe coupled with vars
tPureExp (ABS.EEq l r) = do tl <- tPureExp l;  tr <- tPureExp r; pure [hs|($tl == $tr)|]

-- -- normalizess to not . ==
tPureExp (ABS.ENeq left right) = tPureExp (ABS.ELogNeg $ ABS.EEq left right) 

-- -- be careful to parenthesize infix apps
tPureExp (ABS.EOr l r)   = do tl <- tPureExp l;  tr <- tPureExp r; pure [hs|($tl || $tr)|]
tPureExp (ABS.EAnd l r)  = do tl <- tPureExp l;  tr <- tPureExp r; pure [hs|($tl && $tr)|]
tPureExp (ABS.ELt l r)   = do tl <- tPureExp l;  tr <- tPureExp r; pure [hs|($tl < $tr)|]
tPureExp (ABS.ELe l r)   = do tl <- tPureExp l;  tr <- tPureExp r; pure [hs|($tl <= $tr)|]
tPureExp (ABS.EGt l r)   = do tl <- tPureExp l;  tr <- tPureExp r; pure [hs|($tl > $tr)|]
tPureExp (ABS.EGe l r)   = do tl <- tPureExp l;  tr <- tPureExp r; pure [hs|($tl >= $tr)|]
tPureExp (ABS.EAdd l r)  = do tl <- tPureExp l;  tr <- tPureExp r; pure [hs|($tl + $tr)|]
tPureExp (ABS.ESub l r)  = do tl <- tPureExp l;  tr <- tPureExp r; pure [hs|($tl - $tr)|]
tPureExp (ABS.EMul l r)  = do tl <- tPureExp l;  tr <- tPureExp r; pure [hs|($tl * $tr)|]
tPureExp (ABS.EDiv l r)  = do tl <- tPureExp l;  tr <- tPureExp r; pure [hs|($tl / $tr)|]
tPureExp (ABS.EMod l r)  = do tl <- tPureExp l;  tr <- tPureExp r; pure [hs|($tl % $tr)|]
tPureExp (ABS.ELogNeg e) = do te <- tPureExp e; pure [hs|(not $te)|]
tPureExp (ABS.EIntNeg e) = do te <- tPureExp e; pure [hs|(- $te)|]

tPureExp (ABS.ESinglConstr (ABS.U_ (ABS.U (_,"Unit"))))     = pure [hs|()|]
tPureExp (ABS.ESinglConstr (ABS.U_ (ABS.U (_,"Nil"))))      = pure [hs|[]|]
tPureExp (ABS.ESinglConstr (ABS.U_ (ABS.U (_,"EmptyMap")))) = pure [hs|_emptyMap|]
tPureExp (ABS.ESinglConstr (ABS.U_ (ABS.U (_,"EmptySet")))) = pure [hs|_emptySet|]
tPureExp (ABS.ESinglConstr qu) = pure $ maybeUpException $ HS.Con $ HS.UnQual $ HS.Ident $ showQU qu
  where (modul,ident) = splitQU qu
        maybeUpException = if null modul
                           then case find (\ (SN ident' modul',_) -> ident == ident' && maybe True (not . snd) modul') (M.assocs ?st) of
                                  Just (_,SV Exception _) -> HS.Paren . HS.App [hs|I'.toException|]
                                  _ -> id
                           else case M.lookup (SN ident (Just (modul, True))) ?st of
                                  Just (SV Exception _) -> HS.Paren . HS.App [hs|I'.toException|]
                                  _ -> id
                          
tPureExp (ABS.EParamConstr (ABS.U_ (ABS.U (p,"Triple"))) pexps) =   
    if length pexps == 3
    then HS.Paren . HS.Tuple HS.Boxed <$> mapM tPureExp pexps
    else errorPos p "wrong number of arguments to Triple"
tPureExp (ABS.EParamConstr (ABS.U_ (ABS.U (p,"Pair"))) pexps) = 
    if length pexps == 2
    then HS.Paren . HS.Tuple HS.Boxed <$> mapM tPureExp pexps
    else errorPos p "wrong number of arguments to Pair"
tPureExp (ABS.EParamConstr (ABS.U_ (ABS.U (_,"Cons"))) [l, r]) = do
   tl <- tPureExp l
   tr <- tPureExp r
   pure $ [hs|($tl : $tr)|]
tPureExp (ABS.EParamConstr (ABS.U_ (ABS.U (p,"Cons"))) _) = errorPos p "wrong number of arguments to Cons"
tPureExp (ABS.EParamConstr (ABS.U_ (ABS.U (_,"InsertAssoc"))) [l, r]) = do
  tl <- tPureExp l
  tr <- tPureExp r
  pure $ [hs|(insertAssoc $tl $tr)|]
tPureExp (ABS.EParamConstr (ABS.U_ (ABS.U (p,"InsertAssoc"))) _) = errorPos p "wrong number of arguments to InsertAssoc"
tPureExp (ABS.EParamConstr qu args) = maybeUpException . HS.Paren <$>
                                        foldlM (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                        (HS.Con $ HS.UnQual $ HS.Ident $ showQU qu)
                                        args
  where (modul,ident) = splitQU qu
        maybeUpException = if null modul
                           then case find (\ (SN ident' modul',_) -> ident == ident' && maybe True (not . snd) modul') (M.assocs ?st) of
                                  Just (_,SV Exception _) -> HS.Paren . HS.App [hs|I'.toException|]
                                  _ -> id
                           else case M.lookup (SN ident (Just (modul, True))) ?st of
                                  Just (SV Exception _) -> HS.Paren . HS.App [hs|I'.toException|]
                                  _ -> id
    
tPureExp (ABS.EVar var@(ABS.L (p,pid))) = do
     scope <- ask
     pure $ case M.lookup var scope of
              Just t -> maybeUpcast t $ HS.Var $ HS.UnQual $ HS.Ident pid
              Nothing ->  case M.lookup var ?fields of
                           Just t -> maybeUpcast t $ if null ?cname
                                    then HS.Var $ HS.UnQual $ HS.Ident $ pid ++ "'this" -- errorPos p "cannot access fields inside main block or pure functions"
                                    else let fieldFun = HS.Var $ HS.UnQual $ HS.Ident $ pid ++ "'" ++ ?cname -- accessor
                                         in [hs|($fieldFun this'')|] -- accessor
                           Nothing -> case find (\ (SN ident' modul,_) -> pid == ident' && maybe False (not . snd) modul) (M.assocs ?st) of
                                       Just (_,SV Foreign _) -> HS.Var $ HS.UnQual $ HS.Ident pid
                                       _ ->  HS.Var $ HS.UnQual $ HS.Ident pid -- errorPos p $ pid ++ " not in scope" -- 


tPureExp (ABS.EField var@(ABS.L (p, field))) = case M.lookup var ?fields of
                                                  Just t -> pure $ maybeUpcast t $ if null ?cname
                                                            then HS.Var $ HS.UnQual $ HS.Ident $ field ++ "'this" -- errorPos p "cannot access fields inside main block or pure code"
                                                            else let fieldFun = HS.Var $ HS.UnQual $ HS.Ident $ field ++ "'" ++ ?cname
                                                                 in [hs|($fieldFun this'')|]
                                                  Nothing -> errorPos p "no such field"
  
tPureExp (ABS.ELit lit) = pure $ case lit of
                                   ABS.LStr str ->  HS.Lit $ HS.String str
                                   ABS.LInt i ->  HS.Lit $ HS.Int i
                                   ABS.LFloat f -> HS.Lit $ HS.Frac $ toRational f
                                   ABS.LThis -> if null ?cname
                                               then error "cannot access this keyword inside main block or pure code"
                                               else [hs|(up' this)|]
                                   ABS.LNull -> [hs|(up' null)|]
                                   ABS.LThisDC -> [hs|thisDC|]


-- UPCASTING
------------

-- | upcasting an expression
maybeUpcast :: (?st::SymbolTable) => ABS.T -> HS.Exp -> HS.Exp
maybeUpcast t = case t of
  ABS.TSimple (ABS.U_ (ABS.U (_,"Int"))) -> (\ e -> [hs|(I'.fromIntegral $e)|])
  ABS.TSimple qtyp -> let (prefix, iident) = splitQU qtyp 
                      in case find (\ (SN ident' mmodule,_) -> iident == ident' && maybe (null prefix) ((prefix,True) ==) mmodule) (M.assocs ?st) of
                          Just (_,SV (Interface _ _) _) -> (\ e -> [hs|(up' $e)|]) -- is interface
                          _ -> id
  _ -> id
