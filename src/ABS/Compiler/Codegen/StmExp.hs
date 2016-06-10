{-# LANGUAGE CPP, ImplicitParams, QuasiQuotes #-}
-- | abs-pure-expressions in the statement world (which allows mutable local variables, fields, etc)
-- 
-- the resulting haskell expressions have type IO, which means that eventually later have to be lifted to ABS monad
module ABS.Compiler.Codegen.StmExp
    ( tStmExp
    ) where

import ABS.Compiler.Codegen.Base
import ABS.Compiler.Utils
import ABS.Compiler.Codegen.Typ
import ABS.Compiler.Codegen.Pat
import ABS.Compiler.Firstpass.Base
import qualified ABS.AST as ABS
import qualified Language.Haskell.Exts.Syntax as HS
import Control.Monad.Trans.Reader (local, ask)
import qualified Data.Map as M (insert, lookup, union, assocs)
import Language.Haskell.Exts.QQ (hs)
import Data.Foldable (foldlM)
import Data.List (find)

import Control.Exception (assert)
#define todo assert False (error "not implemented yet")

-- | Translating a pure expression augmented to work with mutable local variables & fields of the statement world
tStmExp :: (?st::SymbolTable, ?vars::ScopeLVL, ?fields::ScopeLVL, ?cname::String)
        => ABS.PureExp -> LetScope HS.Exp

tStmExp (ABS.EIf predE thenE elseE) = do
  tpred <- tStmExp predE
  tthen <- tStmExp thenE
  telse <- tStmExp elseE
  pure $ HS.Do [ HS.Generator noLoc' (HS.PVar $ HS.Ident "if'") tpred
               , HS.Qualifier [hs|if if' then $tthen else $telse|]
               ]

tStmExp (ABS.ELet (ABS.FormalPar ptyp pid@(ABS.L (_,var))) eqE inE) = do
  tin <- local (M.insert pid ptyp) $ tStmExp inE -- adds to scope
  teq <- tStmExp eqE
  let pat = HS.Ident var
  pure $ case ptyp of
             ABS.TInfer -> [hs|(\ ((pat)) -> $tin) =<< $teq|] -- don't add type-sig, infer it
             _ -> let typ = tType ptyp
                 in [hs|(\ ((pat)) -> $tin) =<< ( $teq :: ((typ)) )|] -- maps to a haskell lambda exp

tStmExp (ABS.ECase ofE branches) = do
  tof <- tStmExp ofE
  tcase <- HS.Case (HS.Var $ HS.UnQual $ HS.Ident "of'") <$>
          mapM (\ (ABS.ECaseBranch pat pexp) -> do
                  texp <- tStmExp pexp
                  pure $ HS.Alt noLoc' (tPattern pat) (HS.UnGuardedRhs texp) Nothing
               ) branches
  pure $ HS.Do [ HS.Generator noLoc' (HS.PVar $ HS.Ident "of'") tof
               , HS.Qualifier tcase
               ]

tStmExp (ABS.EFunCall (ABS.QL _ _) _args) = todo

tStmExp (ABS.EFunCall (ABS.L_ (ABS.L (_,cid))) args) =  case find (\ (SN ident' modul,_) -> cid == ident' && maybe False (not . snd) modul) (M.assocs ?st) of
                                                      Just (_,SV Foreign _) -> if null args
                                                                              then pure [hs|$(HS.Var $ HS.UnQual $ HS.Ident cid)|]
                                                                              else do 
                                                                                nested <- foldlM
                                                                                         (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs|($acc <*> $targ)|])
                                                                                         [hs|I'.pure $(HS.Var $ HS.UnQual $ HS.Ident cid)|]
                                                                                         args
                                                                                pure [hs|(I'.join ($nested))|]
                                                      _ ->  HS.Paren <$> foldlM
                                                           (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs|$acc <*> $targ|])
                                                           [hs|I'.pure $(HS.Var $ HS.UnQual $ HS.Ident cid)|]
                                                           args

tStmExp (ABS.ENaryFunCall ql args) = do
    targs <- HS.List <$> mapM tStmExp args
    pure [hs|($(HS.Var $ HS.UnQual $ HS.Ident $ showQL ql) <$!> (I'.sequence $targs))|]


-- constants
tStmExp (ABS.EEq (ABS.ELit ABS.LNull) (ABS.ELit ABS.LNull)) = pure [hs|I'.pure True|]
tStmExp (ABS.EEq (ABS.ELit ABS.LThis) (ABS.ELit ABS.LThis)) = pure [hs|I'.pure True|]
tStmExp (ABS.EEq (ABS.ELit ABS.LNull) (ABS.ELit ABS.LThis)) = pure [hs|I'.pure False|]

-- optimization, to wrap null with the direct interface of rhs instead of up'
tStmExp (ABS.EEq (ABS.ELit ABS.LNull) pvar@(ABS.EVar ident@(ABS.L (p,str)))) = do
   scope <- ask
   tvar <- tStmExp pvar
   pure $ case M.lookup ident (scope `M.union` ?vars `M.union` ?fields) of -- check the type of the right var
            Just (ABS.TSimple qu) -> [hs|((==) ($(HS.Var $ HS.UnQual $ HS.Ident $ showQU qu) null) <$!> $tvar)|]
            Just _ -> errorPos p "cannot equate null to non-interface type"
            Nothing -> errorPos p $ str ++ " variable not in scope or has foreign type"
-- commutative
tStmExp (ABS.EEq pvar@(ABS.EVar _) pnull@(ABS.ELit ABS.LNull)) = tStmExp (ABS.EEq pnull pvar)

-- optimization, to wrap null with the direct interface of rhs instead of up'
tStmExp (ABS.EEq (ABS.ELit ABS.LNull) pvar@(ABS.EField ident@(ABS.L (p,str)))) = do
   tvar <- tStmExp pvar
   pure $ case M.lookup ident ?fields of -- check the type of the right var
            Just (ABS.TSimple qu) -> [hs|((==) ($(HS.Var $ HS.UnQual $ HS.Ident $ showQU qu) null) <$!> $tvar)|]
            Just _ -> errorPos p "cannot equate null to non-interface type"
            Nothing -> errorPos p $ str ++ " not in scope"
-- commutative
tStmExp (ABS.EEq pvar@(ABS.EField _) pnull@(ABS.ELit ABS.LNull)) = tStmExp (ABS.EEq pnull pvar)


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
tStmExp (ABS.EEq l r) = do tl <- tStmExp l;  tr <- tStmExp r; pure [hs|((==) <$!> $tl <*> $tr)|]

-- -- normalizes to not . ==
tStmExp (ABS.ENeq left right) = tStmExp (ABS.ELogNeg $ ABS.EEq left right) 

-- -- be careful to parenthesize infix apps
tStmExp (ABS.EOr l r)   = do tl <- tStmExp l;  tr <- tStmExp r; pure [hs|((||) <$!> $tl <*> $tr)|]
tStmExp (ABS.EAnd l r)  = do tl <- tStmExp l;  tr <- tStmExp r; pure [hs|((^) <$!> $tl <*> $tr)|]
tStmExp (ABS.ELt l r)   = do tl <- tStmExp l;  tr <- tStmExp r; pure [hs|((<) <$!> $tl <*> $tr)|]
tStmExp (ABS.ELe l r)   = do tl <- tStmExp l;  tr <- tStmExp r; pure [hs|((<=) <$!> $tl <*> $tr)|]
tStmExp (ABS.EGt l r)   = do tl <- tStmExp l;  tr <- tStmExp r; pure [hs|((>) <$!> $tl <*> $tr)|]
tStmExp (ABS.EGe l r)   = do tl <- tStmExp l;  tr <- tStmExp r; pure [hs|((>=) <$!> $tl <*> $tr)|]
tStmExp (ABS.EAdd l r)  = do tl <- tStmExp l;  tr <- tStmExp r; pure [hs|((+) <$!> $tl <*> $tr)|]
tStmExp (ABS.ESub l r)  = do tl <- tStmExp l;  tr <- tStmExp r; pure [hs|((-) <$!> $tl <*> $tr)|]
tStmExp (ABS.EMul l r)  = do tl <- tStmExp l;  tr <- tStmExp r; pure [hs|((*) <$!> $tl <*> $tr)|]
tStmExp (ABS.EDiv l r)  = do tl <- tStmExp l;  tr <- tStmExp r; pure [hs|((/) <$!> $tl <*> $tr)|]
tStmExp (ABS.EMod l r)  = do tl <- tStmExp l;  tr <- tStmExp r; pure [hs|((%) <$!> $tl <*> $tr)|]
tStmExp (ABS.ELogNeg e) = do te <- tStmExp e; pure [hs|((not) <$!> $te)|]
tStmExp (ABS.EIntNeg e) = do te <- tStmExp e; pure [hs|(I'.negate <$!> $te)|]

tStmExp (ABS.ESinglConstr (ABS.U_ (ABS.U (_,"Unit"))))     = pure [hs|I'.pure ()|]
tStmExp (ABS.ESinglConstr (ABS.U_ (ABS.U (_,"Nil"))))      = pure [hs|I'.pure []|]
tStmExp (ABS.ESinglConstr (ABS.U_ (ABS.U (_,"EmptyMap")))) = pure [hs|I'.pure _emptyMap|]
tStmExp (ABS.ESinglConstr (ABS.U_ (ABS.U (_,"EmptySet")))) = pure [hs|I'.pure _emptySet|]
tStmExp (ABS.ESinglConstr qu) = pure [hs|I'.pure $(maybeUpException $ HS.Con $ HS.UnQual $ HS.Ident $ showQU qu)|]
  where (modul,ident) = splitQU qu
        maybeUpException = if null modul
                           then case find (\ (SN ident' modul',_) -> ident == ident' && maybe True (not . snd) modul') (M.assocs ?st) of
                                  Just (_,SV Exception _) -> HS.Paren . HS.App [hs|I'.SomeException|]
                                  _ -> id
                           else case M.lookup (SN ident (Just (modul, True))) ?st of
                                  Just (SV Exception _) -> HS.Paren . HS.App [hs|I'.SomeException|]
                                  _ -> id

tStmExp (ABS.EParamConstr (ABS.U_ (ABS.U (p,"Triple"))) pexps) =   
    if length pexps == 3
    then do
      let [pexp1,pexp2,pexp3] = pexps
      texp1 <- tStmExp pexp1
      texp2 <- tStmExp pexp2
      texp3 <- tStmExp pexp3
      pure [hs|((,,) <$!> $texp1 <*> $texp2 <*> $texp3)|]
    else errorPos p "wrong number of arguments to Triple"
tStmExp (ABS.EParamConstr (ABS.U_ (ABS.U (p,"Pair"))) pexps) = 
    if length pexps == 2
    then do
      let [pexp1,pexp2] = pexps
      texp1 <- tStmExp pexp1
      texp2 <- tStmExp pexp2
      pure [hs|((,) <$!> $texp1 <*> $texp2)|]
    else errorPos p "wrong number of arguments to Pair"
tStmExp (ABS.EParamConstr (ABS.U_ (ABS.U (_,"Cons"))) [l, r]) = do
   tl <- tStmExp l
   tr <- tStmExp r
   pure $ [hs|((:) <$!> $tl <*> $tr)|]
tStmExp (ABS.EParamConstr (ABS.U_ (ABS.U (p,"Cons"))) _) = errorPos p "wrong number of arguments to Cons"
tStmExp (ABS.EParamConstr (ABS.U_ (ABS.U (_,"InsertAssoc"))) [l, r]) = do
  tl <- tStmExp l
  tr <- tStmExp r
  pure $ [hs|(insertAssoc <$!> $tl <*> $tr)|]
tStmExp (ABS.EParamConstr (ABS.U_ (ABS.U (p,"InsertAssoc"))) _) = errorPos p "wrong number of arguments to InsertAssoc"
tStmExp (ABS.EParamConstr qu args) = maybeUpException . HS.Paren <$>
    foldlM
    (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs|$acc <*> $targ|])
    [hs|I'.pure $(HS.Con $ HS.UnQual $ HS.Ident $ showQU qu)|]
    args
  where (modul,ident) = splitQU qu
        maybeUpException = if null modul
                           then case find (\ (SN ident' modul',_) -> ident == ident' && maybe True (not . snd) modul') (M.assocs ?st) of
                                  Just (_,SV Exception _) -> HS.Paren . HS.InfixApp [hs|I'.SomeException|] (HS.QConOp $ HS.UnQual $ HS.Symbol "<$!>")
                                  _ -> id
                           else case M.lookup (SN ident (Just (modul, True))) ?st of
                                  Just (SV Exception _) -> HS.Paren . HS.InfixApp [hs|I'.SomeException|] (HS.QConOp $ HS.UnQual $ HS.Symbol "<$!>")
                                  _ -> id
                                 
tStmExp (ABS.EVar var@(ABS.L (p,pid))) = do
     scope <- ask
     pure $ case M.lookup var scope of
              Just t -> maybePureUpcast t $ HS.Var $ HS.UnQual $ HS.Ident pid
              Nothing -> case M.lookup var ?vars of
                          Just t -> maybeEffUpcast t [hs|I'.readIORef $(HS.Var $ HS.UnQual $ HS.Ident pid)|]
                          Nothing -> case M.lookup var ?fields of
                                    Just t -> let fieldFun = HS.Var $ HS.UnQual $ HS.Ident $ pid ++ "'" ++ ?cname -- accessor
                                             in maybePureUpcast t [hs|($fieldFun this'')|]
                                    Nothing-> case find (\ (SN ident' modul,_) -> pid == ident' && maybe False (not . snd) modul) (M.assocs ?st) of
                                               Just (_,SV Foreign _) -> HS.Var $ HS.UnQual $ HS.Ident pid
                                               _ ->  [hs|I'.pure $(HS.Var $ HS.UnQual $ HS.Ident pid)|] -- errorPos p $ pid ++ " not in scope" --  -- 


tStmExp (ABS.EField var@(ABS.L (p, field))) = if null ?cname
                                                  then error "cannot access fields inside main block"
                                                  else case M.lookup var ?fields of
                                                         Just t -> let fieldFun = HS.Var $ HS.UnQual $ HS.Ident $ field ++ "'" ++ ?cname
                                                                  in pure $ maybePureUpcast t [hs|($fieldFun this'')|]
                                                         Nothing -> errorPos p "no such field"

tStmExp (ABS.ELit lit) = pure $ case lit of
                                   ABS.LStr str ->  [hs|I'.pure $(HS.Lit $ HS.String str)|]
                                   ABS.LInt i ->  [hs|I'.pure $(HS.Lit $ HS.Int i)|]
                                   ABS.LFloat f -> [hs|I'.pure $(HS.Lit $ HS.Frac $ toRational f)|]
                                   ABS.LThis -> if null ?cname
                                               then error "cannot access this keyword inside main block"
                                               else [hs|I'.pure (up' this)|]
                                   ABS.LNull -> [hs|I'.pure (up' null)|]
                                   ABS.LThisDC -> [hs|I'.pure thisDC|]



-- UPCASTING
------------

-- | upcasting an expression
maybePureUpcast :: (?st::SymbolTable) => ABS.T -> HS.Exp -> HS.Exp
maybePureUpcast t = case t of
  ABS.TSimple (ABS.U_ (ABS.U (_,"Int"))) -> (\ e -> [hs|I'.pure (I'.fromIntegral $e)|])
  ABS.TSimple qtyp -> let (prefix, iident) = splitQU qtyp 
                     in case find (\ (SN ident' mmodule,_) -> iident == ident' && maybe (null prefix) ((prefix,True) ==) mmodule) (M.assocs ?st) of
                          Just (_,SV (Interface _ _) _) -> (\ e -> [hs|I'.pure (up' $e)|]) -- is interface
                          _ -> (\ e -> [hs|I'.pure $e|])
  _ -> (\ e -> [hs|I'.pure $e|])


maybeEffUpcast :: (?st::SymbolTable) => ABS.T -> HS.Exp -> HS.Exp
maybeEffUpcast t = case t of
  ABS.TSimple (ABS.U_ (ABS.U (_,"Int"))) -> (\ e -> [hs|(I'.fromIntegral <$!> $e)|])
  ABS.TSimple qtyp -> let (prefix, iident) = splitQU qtyp 
                     in case find (\ (SN ident' mmodule,_) -> iident == ident' && maybe (null prefix) ((prefix,True) ==) mmodule) (M.assocs ?st) of
                          Just (_,SV (Interface _ _) _) -> (\ e -> [hs|(up' <$!> $e)|]) -- is interface
                          _ -> id
  _ -> id
