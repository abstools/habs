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
        => ABS.PureExp -> LetScope (HS.Exp, [ABS.T])

tStmExp (ABS.EIf predE thenE elseE) = do
  (tpred,_) <- tStmExp predE
  (tthen,_) <- tStmExp thenE
  (telse,_) <- tStmExp elseE
  pure (HS.Do [ HS.Generator noLoc' (HS.PVar $ HS.Ident "if'") tpred
              , HS.Qualifier [hs|if if' then $tthen else $telse|]
              ]
       ,[ABS.TSimple $ ABS.U_ $ ABS.U ((0,0),"Bool")])

tStmExp (ABS.ELet (ABS.FormalPar ptyp pid@(ABS.L (_,var))) eqE inE) = do
  (tin,_) <- local (M.insert pid ptyp) $ tStmExp inE -- adds to scope
  (teq,_) <- tStmExp eqE
  let pat = HS.Ident var
  pure (case ptyp of
             ABS.TInfer -> [hs|(\ ((pat)) -> $tin) =<< $teq|] -- don't add type-sig, infer it
             _ -> let typ = tType ptyp
                 in [hs|(\ ((pat)) -> $tin) =<< ( $teq :: ((typ)) )|] -- maps to a haskell lambda exp
       ,[ptyp])

tStmExp (ABS.ECase ofE branches) = do
  (tof,_) <- tStmExp ofE
  tcase <- HS.Case (HS.Var $ HS.UnQual $ HS.Ident "of'") <$>
          mapM (\ (ABS.ECaseBranch pat pexp) -> do
                  (texp,_) <- tStmExp pexp
                  (tpat,_) <- tPattern pat
                  pure $ HS.Alt noLoc' tpat (HS.UnGuardedRhs texp) Nothing
               ) branches
  pure (HS.Do [ HS.Generator noLoc' (HS.PVar $ HS.Ident "of'") tof
              , HS.Qualifier tcase
              ]
       ,undefined)

tStmExp (ABS.EFunCall (ABS.QL _ _) _args) = todo

tStmExp (ABS.EFunCall (ABS.L_ (ABS.L (_,cid))) args) =  case find (\ (SN ident' modul,_) -> cid == ident' && maybe False (not . snd) modul) (M.assocs ?st) of
                                                      Just (_,SV Foreign _) -> if null args
                                                                              then pure ([hs|$(HS.Var $ HS.UnQual $ HS.Ident cid)|], undefined)
                                                                              else do 
                                                                                nested <- foldlM
                                                                                         (\ acc nextArg -> tStmExp nextArg >>= \ (targ,_) -> pure [hs|($acc <*> $targ)|])
                                                                                         [hs|I'.pure $(HS.Var $ HS.UnQual $ HS.Ident cid)|]
                                                                                         args
                                                                                pure ([hs|(I'.join ($nested))|], undefined)
                                                      _ -> (\ x -> (x,undefined)) . HS.Paren <$> foldlM
                                                           (\ acc nextArg -> tStmExp nextArg >>= \ (targ,_) -> pure [hs|$acc <*> $targ|])
                                                           [hs|I'.pure $(HS.Var $ HS.UnQual $ HS.Ident cid)|]
                                                           args

tStmExp (ABS.ENaryFunCall ql args) = do
    targs <- HS.List . map fst <$> mapM tStmExp args
    pure ([hs|($(HS.Var $ HS.UnQual $ HS.Ident $ showQL ql) <$!> (I'.sequence $targs))|], undefined)


-- constants
tStmExp (ABS.EEq (ABS.ELit ABS.LNull) (ABS.ELit ABS.LNull)) = pure ([hs|I'.pure True|], [ABS.TSimple $ ABS.U_ $ ABS.U ((0,0),"Bool")])
tStmExp (ABS.EEq (ABS.ELit ABS.LThis) (ABS.ELit ABS.LThis)) = pure ([hs|I'.pure True|], [ABS.TSimple $ ABS.U_ $ ABS.U ((0,0),"Bool")])
tStmExp (ABS.EEq (ABS.ELit ABS.LNull) (ABS.ELit ABS.LThis)) = pure ([hs|I'.pure False|], [ABS.TSimple $ ABS.U_ $ ABS.U ((0,0),"Bool")])

-- optimization, to wrap null with the direct interface of rhs instead of up'
tStmExp (ABS.EEq (ABS.ELit ABS.LNull) pvar@(ABS.EVar ident@(ABS.L (p,str)))) = do
   scope <- ask
   (tvar,_) <- tStmExp pvar
   pure $ case M.lookup ident (scope `M.union` ?vars `M.union` ?fields) of -- check the type of the right var
            Just (ABS.TSimple qu) -> ([hs|((==) ($(HS.Var $ HS.UnQual $ HS.Ident $ showQU qu) null) <$!> $tvar)|], undefined)
            Just _ -> errorPos p "cannot equate null to non-interface type"
            Nothing -> errorPos p $ str ++ " variable not in scope or has foreign type"
-- commutative
tStmExp (ABS.EEq pvar@(ABS.EVar _) pnull@(ABS.ELit ABS.LNull)) = tStmExp (ABS.EEq pnull pvar)

-- optimization, to wrap null with the direct interface of rhs instead of up'
tStmExp (ABS.EEq (ABS.ELit ABS.LNull) pvar@(ABS.EField ident@(ABS.L (p,str)))) = do
   (tvar,_) <- tStmExp pvar
   pure $ case M.lookup ident ?fields of -- check the type of the right var
            Just (ABS.TSimple qu) -> ([hs|((==) ($(HS.Var $ HS.UnQual $ HS.Ident $ showQU qu) null) <$!> $tvar)|],[ABS.TSimple $ ABS.U_ $ ABS.U ((0,0),"Bool")])
            Just _ -> errorPos p "cannot equate null to non-interface type"
            Nothing -> errorPos p $ str ++ " not in scope"
-- commutative
tStmExp (ABS.EEq pvar@(ABS.EField _) pnull@(ABS.ELit ABS.LNull)) = tStmExp (ABS.EEq pnull pvar)

-- a catch-all for literals,constructors maybe coupled with vars
tStmExp (ABS.EEq l r) = do (tl,_) <- tStmExp l;  (tr,_) <- tStmExp r; pure ([hs|((==) <$!> $tl <*> $tr)|], [ABS.TSimple $ ABS.U_ $ ABS.U ((0,0),"Bool")])

-- -- normalizes to not . ==
tStmExp (ABS.ENeq left right) = tStmExp (ABS.ELogNeg $ ABS.EEq left right) 

-- -- be careful to parenthesize infix apps
tStmExp (ABS.EOr l r)   = do (tl,_) <- tStmExp l;  (tr,_) <- tStmExp r; pure ([hs|((||) <$!> $tl <*> $tr)|], [ABS.TSimple $ ABS.U_ $ ABS.U ((0,0),"Bool")])
tStmExp (ABS.EAnd l r)  = do (tl,_) <- tStmExp l;  (tr,_) <- tStmExp r; pure ([hs|((&&) <$!> $tl <*> $tr)|], [ABS.TSimple $ ABS.U_ $ ABS.U ((0,0),"Bool")])
tStmExp (ABS.ELt l r)   = do (tl,_) <- tStmExp l;  (tr,_) <- tStmExp r; pure ([hs|((<) <$!> $tl <*> $tr)|], [ABS.TSimple $ ABS.U_ $ ABS.U ((0,0),"Bool")])
tStmExp (ABS.ELe l r)   = do (tl,_) <- tStmExp l;  (tr,_) <- tStmExp r; pure ([hs|((<=) <$!> $tl <*> $tr)|], [ABS.TSimple $ ABS.U_ $ ABS.U ((0,0),"Bool")])
tStmExp (ABS.EGt l r)   = do (tl,_) <- tStmExp l;  (tr,_) <- tStmExp r; pure ([hs|((>) <$!> $tl <*> $tr)|], [ABS.TSimple $ ABS.U_ $ ABS.U ((0,0),"Bool")])
tStmExp (ABS.EGe l r)   = do (tl,_) <- tStmExp l;  (tr,_) <- tStmExp r; pure ([hs|((>=) <$!> $tl <*> $tr)|], [ABS.TSimple $ ABS.U_ $ ABS.U ((0,0),"Bool")])
tStmExp (ABS.EAdd l r)  = do (tl,_) <- tStmExp l;  (tr,_) <- tStmExp r; pure ([hs|((+) <$!> $tl <*> $tr)|], undefined)
tStmExp (ABS.ESub l r)  = do (tl,_) <- tStmExp l;  (tr,_) <- tStmExp r; pure ([hs|((-) <$!> $tl <*> $tr)|], undefined)
tStmExp (ABS.EMul l r)  = do (tl,_) <- tStmExp l;  (tr,_) <- tStmExp r; pure ([hs|((*) <$!> $tl <*> $tr)|], undefined)
tStmExp (ABS.EDiv l r)  = do (tl,_) <- tStmExp l;  (tr,_) <- tStmExp r; pure ([hs|((/) <$!> $tl <*> $tr)|], [ABS.TSimple $ ABS.U_ $ ABS.U ((0,0),"Rat")])
tStmExp (ABS.EMod l r)  = do (tl,_) <- tStmExp l;  (tr,_) <- tStmExp r; pure ([hs|((%) <$!> $tl <*> $tr)|], undefined)
tStmExp (ABS.ELogNeg e) = do (te,_) <- tStmExp e; pure ([hs|(not <$!> $te)|], [ABS.TSimple $ ABS.U_ $ ABS.U ((0,0),"Bool")])
tStmExp (ABS.EIntNeg e) = do (te,_) <- tStmExp e; pure ([hs|(I'.negate <$!> $te)|], undefined)

tStmExp (ABS.ESinglConstr (ABS.U_ (ABS.U (_,"Unit"))))     = pure ([hs|I'.pure ()|], [ABS.TSimple $ ABS.U_ $ ABS.U ((0,0),"Unit")])
tStmExp (ABS.ESinglConstr (ABS.U_ (ABS.U (_,"Nil"))))      = pure ([hs|I'.pure []|], undefined)
tStmExp (ABS.ESinglConstr (ABS.U_ (ABS.U (_,"EmptyMap")))) = pure ([hs|I'.pure _emptyMap|], undefined)
tStmExp (ABS.ESinglConstr (ABS.U_ (ABS.U (_,"EmptySet")))) = pure ([hs|I'.pure _emptySet|], undefined)
tStmExp (ABS.ESinglConstr qu) = pure ([hs|I'.pure $(maybeUpException $ HS.Con $ HS.UnQual $ HS.Ident $ showQU qu)|], undefined)
  where (modul,ident) = splitQU qu
        maybeUpException = if null modul
                           then case find (\ (SN ident' modul',_) -> ident == ident' && maybe True (not . snd) modul') (M.assocs ?st) of
                                  Just (_,SV Exception _) -> HS.Paren . HS.App [hs|I'.toException|]
                                  _ -> id
                           else case M.lookup (SN ident (Just (modul, True))) ?st of
                                  Just (SV Exception _) -> HS.Paren . HS.App [hs|I'.toException|]
                                  _ -> id

tStmExp (ABS.EParamConstr (ABS.U_ (ABS.U (p,"Triple"))) pexps) =   
    if length pexps == 3
    then do
      let [pexp1,pexp2,pexp3] = pexps
      (texp1, _) <- tStmExp pexp1
      (texp2, _) <- tStmExp pexp2
      (texp3, _) <- tStmExp pexp3
      pure ([hs|((,,) <$!> $texp1 <*> $texp2 <*> $texp3)|], undefined)
    else errorPos p "wrong number of arguments to Triple"
tStmExp (ABS.EParamConstr (ABS.U_ (ABS.U (p,"Pair"))) pexps) = 
    if length pexps == 2
    then do
      let [pexp1,pexp2] = pexps
      (texp1, _) <- tStmExp pexp1
      (texp2, _) <- tStmExp pexp2
      pure ([hs|((,) <$!> $texp1 <*> $texp2)|], undefined)
    else errorPos p "wrong number of arguments to Pair"
tStmExp (ABS.EParamConstr (ABS.U_ (ABS.U (_,"Cons"))) [l, r]) = do
   (tl,_) <- tStmExp l
   (tr,_) <- tStmExp r
   pure ([hs|((:) <$!> $tl <*> $tr)|], undefined)
tStmExp (ABS.EParamConstr (ABS.U_ (ABS.U (p,"Cons"))) _) = errorPos p "wrong number of arguments to Cons"
tStmExp (ABS.EParamConstr (ABS.U_ (ABS.U (_,"InsertAssoc"))) [l, r]) = do
  (tl,_) <- tStmExp l
  (tr,_) <- tStmExp r
  pure ([hs|(insertAssoc <$!> $tl <*> $tr)|], undefined)
tStmExp (ABS.EParamConstr (ABS.U_ (ABS.U (p,"InsertAssoc"))) _) = errorPos p "wrong number of arguments to InsertAssoc"
tStmExp (ABS.EParamConstr qu args) = (\x -> (x,undefined)) .  maybeUpException . HS.Paren <$>
    foldlM
    (\ acc nextArg -> tStmExp nextArg >>= \ (targ,_) -> pure [hs|$acc <*> $targ|])
    [hs|I'.pure $(HS.Con $ HS.UnQual $ HS.Ident $ showQU qu)|]
    args
  where (modul,ident) = splitQU qu
        maybeUpException = if null modul
                           then case find (\ (SN ident' modul',_) -> ident == ident' && maybe True (not . snd) modul') (M.assocs ?st) of
                                  Just (_,SV Exception _) -> HS.Paren . HS.InfixApp [hs|I'.toException|] (HS.QConOp $ HS.UnQual $ HS.Symbol "<$!>")
                                  _ -> id
                           else case M.lookup (SN ident (Just (modul, True))) ?st of
                                  Just (SV Exception _) -> HS.Paren . HS.InfixApp [hs|I'.toException|] (HS.QConOp $ HS.UnQual $ HS.Symbol "<$!>")
                                  _ -> id
                                 
tStmExp (ABS.EVar var@(ABS.L (p,pid))) = do
     scope <- ask
     pure $ case M.lookup var scope of
              Just t -> (HS.Var $ HS.UnQual $ HS.Ident pid, undefined)
              Nothing -> case M.lookup var ?vars of
                          Just t -> ([hs|I'.readIORef $(HS.Var $ HS.UnQual $ HS.Ident pid)|], undefined)
                          Nothing -> case M.lookup var ?fields of
                                    Just t -> let fieldFun = HS.Var $ HS.UnQual $ HS.Ident $ pid ++ "'" ++ ?cname -- accessor
                                             in ([hs|($fieldFun this'')|], undefined)
                                    Nothing-> case find (\ (SN ident' modul,_) -> pid == ident' && maybe False (not . snd) modul) (M.assocs ?st) of
                                               Just (_,SV Foreign _) -> (HS.Var $ HS.UnQual $ HS.Ident pid, undefined)
                                               _ ->  ([hs|I'.pure $(HS.Var $ HS.UnQual $ HS.Ident pid)|], undefined) -- errorPos p $ pid ++ " not in scope" --  -- 


tStmExp (ABS.EField var@(ABS.L (p, field))) = if null ?cname
                                                  then error "cannot access fields inside main block"
                                                  else case M.lookup var ?fields of
                                                         Just t -> let fieldFun = HS.Var $ HS.UnQual $ HS.Ident $ field ++ "'" ++ ?cname
                                                                  in pure ([hs|($fieldFun this'')|], undefined)
                                                         Nothing -> errorPos p "no such field"

tStmExp (ABS.ELit lit) = pure $ case lit of
                                   ABS.LStr str -> ([hs|I'.pure $(HS.Lit $ HS.String str)|], [ABS.TSimple $ ABS.U_ $ ABS.U ((0,0),"String")])
                                   ABS.LInt i ->  ([hs|I'.pure $(HS.Lit $ HS.Int i)|], map (ABS.TSimple . ABS.U_ . ABS.U . (,) (0,0)) ["Int","Rat"])
                                   ABS.LThis -> if null ?cname
                                               then error "cannot access this keyword inside main block"
                                               else ([hs|I'.pure (up' this)|], undefined)
                                   ABS.LNull -> ([hs|I'.pure (up' null)|], [ABS.TInfer])