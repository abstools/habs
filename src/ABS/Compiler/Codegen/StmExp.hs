{-# LANGUAGE CPP, ImplicitParams, QuasiQuotes, LambdaCase #-}
-- | abs-pure-expressions in the statement world (which allows mutable local variables, fields, etc)
-- 
-- the resulting haskell expressions have type IO, which means that eventually later have to be lifted to ABS monad
module ABS.Compiler.Codegen.StmExp
    ( tStmExp
    , mUpOne
    ) where

import ABS.Compiler.Codegen.Base
import ABS.Compiler.Utils
import ABS.Compiler.Codegen.Typ
import ABS.Compiler.Codegen.Pat
import ABS.Compiler.Firstpass.Base
import qualified ABS.AST as ABS
import qualified Language.Haskell.Exts.Syntax as HS
import Control.Monad.Trans.Reader (local, ask)
import qualified Data.Map as M (insert, lookup, union, assocs, findWithDefault)
import Language.Haskell.Exts.QQ (hs)
import Data.Foldable (foldlM)
import Data.List (find)

import Control.Exception (assert)
#define todo assert False (error "not implemented yet")

-- | Translating a pure expression augmented to work with mutable local variables & fields of the statement world
tStmExp :: (?st::SymbolTable, ?vars::ScopeLVL, ?fields::ScopeLVL, ?cname::String)
        => ABS.PureExp -> LetScope (HS.Exp, ABS.T)

tStmExp (ABS.EIf predE thenE elseE) = do
  (ep,_) <- tStmExp predE
  (e1,t1) <- tStmExp thenE
  (e2,t2) <- tStmExp elseE
  let freshTyVar = ABS.U ((0,0),"A'")
      declaredArgs = [ABS.TSimple (ABS.U_ freshTyVar), ABS.TSimple (ABS.U_ freshTyVar)]
      bs = unifyMany [freshTyVar] declaredArgs [t1,t2]
      instantArgs = instantiateMany bs declaredArgs
      instantRes = instantiateOne bs $ ABS.TSimple (ABS.U_ freshTyVar)
      [ue1,ue2] = mUpMany instantArgs [t1,t2] [e1,e2]
  pure (HS.Do [ HS.Generator noLoc' (HS.PVar $ HS.Ident "if'") ep
              , HS.Qualifier [hs|if if' then $ue1 else $ue2|]
              ]
       ,instantRes)

tStmExp (ABS.ELet (ABS.FormalPar ptyp pid@(ABS.L (_,var))) eqE inE) = do
  (ein,tin) <- local (M.insert pid ptyp) $ tStmExp inE -- adds to scope
  (eeq,teq) <- tStmExp eqE
  let pat = HS.Ident var
  pure ([hs|(\ ((pat)) -> $ein) =<< ( $(mUpOne ptyp teq eeq) )|]
       ,tin)

tStmExp (ABS.ECase ofE branches) = do
  (tof,_) <- tStmExp ofE
  (es,ts) <- unzip <$> mapM (\case (ABS.ECaseBranch _ pexp) -> tStmExp pexp) branches
  let freshTyVar = ABS.U ((0,0),"A'")
      declaredRes = replicate (length branches) (ABS.TSimple (ABS.U_ freshTyVar))
      bs = unifyMany [freshTyVar] declaredRes ts
      instantRes = instantiateMany bs declaredRes
      es' = mUpMany instantRes ts es
  tbranches <- mapM (\ (ABS.ECaseBranch pat _, texp') -> do
                      (tpat,tguards) <- tPattern pat
                      pure $ HS.Alt noLoc' tpat ((if null tguards then HS.UnGuardedRhs else (HS.GuardedRhss . pure . HS.GuardedRhs noLoc' tguards)) texp') Nothing
                    ) (zip branches es')
  pure (HS.Do [ HS.Generator noLoc' (HS.PVar $ HS.Ident "of'") tof
              , HS.Qualifier (HS.Case (HS.Var $ HS.UnQual $ HS.Ident "of'") tbranches)
              ]
       ,M.findWithDefault ABS.TInfer "A'" bs)

tStmExp (ABS.EFunCall (ABS.QL _ _) _args) = todo

tStmExp (ABS.EFunCall (ABS.L_ (ABS.L (_,cid))) args) =  
  -- case find (\ (SN ident' modul,_) -> cid == ident' && maybe False (not . snd) modul) (M.assocs ?st) of
  case M.lookup (SN cid Nothing) ?st of
    Just (SV Foreign _) -> if null args
                             then pure ([hs|$(HS.Var $ HS.UnQual $ HS.Ident cid)|], ABS.TInfer)
                             else do 
                              nested <- foldlM
                               (\ acc nextArg -> tStmExp nextArg >>= \ (targ,_) -> pure [hs|($acc <*> $targ)|])
                               [hs|I'.pure $(HS.Var $ HS.UnQual $ HS.Ident cid)|]
                               args
                              pure ([hs|(I'.join ($nested))|], ABS.TInfer)
    Just (SV (Function tyvars declaredArgs declaredRes) _) -> do
      (es,ts) <- unzip <$> mapM tStmExp args
      let bs = unifyMany tyvars declaredArgs ts
          instantArgs = instantiateMany bs declaredArgs
          instantRes = instantiateOne bs declaredRes
          es' = mUpMany instantArgs ts es
      pure (HS.Paren $ foldl (\acc arg -> [hs|$acc <*> $arg|])
                          [hs|I'.pure $(HS.Var $ HS.UnQual $ HS.Ident cid)|]
                          es', instantRes)
    _ -> error $ "cannot find function " ++ cid

tStmExp (ABS.ENaryFunCall ql args) = do
    (es,ts) <- unzip <$> mapM tStmExp args
    let ABS.L_ (ABS.L (_,funName))= ql
    case M.lookup (SN funName Nothing) ?st of
      Just (SV (Function tyvars declaredArgs declaredRes) _) -> do
        let bs = unifyMany tyvars declaredArgs [ABS.TPoly (ABS.U_ $ ABS.U ((0,0),"List")) ts]
            instantArgs = instantiateMany bs declaredArgs
            instantRes = instantiateOne bs declaredRes
            es' = mUpMany instantArgs [ABS.TPoly (ABS.U_ $ ABS.U ((0,0),"List")) ts] es
        pure ([hs|($(HS.Var $ HS.UnQual $ HS.Ident $ showQL ql) <$!> (I'.sequence $(HS.List es')))|], instantRes)
      _ -> error $ "cannot find function " ++ funName


-- constants
tStmExp (ABS.EEq (ABS.ELit ABS.LNull) (ABS.ELit ABS.LNull)) = pure ([hs|I'.pure True|], ABS.TSimple $ ABS.U_ $ ABS.U ((0,0),"Bool"))
tStmExp (ABS.EEq (ABS.ELit ABS.LThis) (ABS.ELit ABS.LThis)) = pure ([hs|I'.pure True|], ABS.TSimple $ ABS.U_ $ ABS.U ((0,0),"Bool"))
tStmExp (ABS.EEq (ABS.ELit ABS.LNull) (ABS.ELit ABS.LThis)) = pure ([hs|I'.pure False|], ABS.TSimple $ ABS.U_ $ ABS.U ((0,0),"Bool"))

-- optimization, to wrap null with the direct interface of rhs instead of up'
tStmExp (ABS.EEq (ABS.ELit ABS.LNull) pvar@(ABS.EVar ident@(ABS.L (p,str)))) = do
   scope <- ask
   (tvar,_) <- tStmExp pvar
   pure $ case M.lookup ident (scope `M.union` ?vars `M.union` ?fields) of -- check the type of the right var
            Just (ABS.TSimple qu) -> ([hs|((==) ($(HS.Var $ HS.UnQual $ HS.Ident $ showQU qu) null) <$!> $tvar)|], ABS.TSimple $ ABS.U_ $ ABS.U ((0,0),"Bool"))
            Just _ -> errorPos p "cannot equate null to non-interface type"
            Nothing -> errorPos p $ str ++ " variable not in scope or has foreign type"
-- commutative
tStmExp (ABS.EEq pvar@(ABS.EVar _) pnull@(ABS.ELit ABS.LNull)) = tStmExp (ABS.EEq pnull pvar)

-- optimization, to wrap null with the direct interface of rhs instead of up'
tStmExp (ABS.EEq (ABS.ELit ABS.LNull) pvar@(ABS.EField ident@(ABS.L (p,str)))) = do
   (tvar,_) <- tStmExp pvar
   pure $ case M.lookup ident ?fields of -- check the type of the right var
            Just (ABS.TSimple qu) -> ([hs|((==) ($(HS.Var $ HS.UnQual $ HS.Ident $ showQU qu) null) <$!> $tvar)|],ABS.TSimple $ ABS.U_ $ ABS.U ((0,0),"Bool"))
            Just _ -> errorPos p "cannot equate null to non-interface type"
            Nothing -> errorPos p $ str ++ " not in scope"
-- commutative
tStmExp (ABS.EEq pvar@(ABS.EField _) pnull@(ABS.ELit ABS.LNull)) = tStmExp (ABS.EEq pnull pvar)

-- a catch-all for literals,constructors maybe coupled with vars
tStmExp (ABS.EEq l r) = do
  (e1,t1) <- tStmExp l
  (e2,t2) <- tStmExp r;
  let freshTyVar = ABS.U ((0,0),"A'")
      declaredArgs = [ABS.TSimple (ABS.U_ freshTyVar), ABS.TSimple (ABS.U_ freshTyVar)]
      instantArgs = instantiateMany (unifyMany [freshTyVar] declaredArgs [t1,t2]) declaredArgs
      [ue1,ue2] = mUpMany instantArgs [t1,t2] [e1,e2]
  pure ([hs|((==) <$!> $ue1 <*> $ue2)|], ABS.TSimple $ ABS.U_ $ ABS.U ((0,0),"Bool"))

-- -- normalizes to not . ==
tStmExp (ABS.ENeq left right) = tStmExp (ABS.ELogNeg $ ABS.EEq left right) 

-- -- be careful to parenthesize infix apps
tStmExp (ABS.EOr l r)   = do (tl,_) <- tStmExp l;  (tr,_) <- tStmExp r; pure ([hs|((||) <$!> $tl <*> $tr)|], ABS.TSimple $ ABS.U_ $ ABS.U ((0,0),"Bool"))
tStmExp (ABS.EAnd l r)  = do (tl,_) <- tStmExp l;  (tr,_) <- tStmExp r; pure ([hs|((&&) <$!> $tl <*> $tr)|], ABS.TSimple $ ABS.U_ $ ABS.U ((0,0),"Bool"))

tStmExp (ABS.ELt l r)   = do
  (e1,t1) <- tStmExp l
  (e2,t2) <- tStmExp r
  let freshTyVar = ABS.U ((0,0),"A'")
      declaredArgs = [ABS.TSimple (ABS.U_ freshTyVar), ABS.TSimple (ABS.U_ freshTyVar)]
      instantArgs = instantiateMany (unifyMany [freshTyVar] declaredArgs [t1,t2]) declaredArgs
      [ue1,ue2] = mUpMany instantArgs [t1,t2] [e1,e2]
  pure ([hs|((<) <$!> $ue1 <*> $ue2)|], ABS.TSimple $ ABS.U_ $ ABS.U ((0,0),"Bool"))
tStmExp (ABS.ELe l r)   = do
  (e1,t1) <- tStmExp l
  (e2,t2) <- tStmExp r
  let freshTyVar = ABS.U ((0,0),"A'")
      declaredArgs = [ABS.TSimple (ABS.U_ freshTyVar), ABS.TSimple (ABS.U_ freshTyVar)]
      instantArgs = instantiateMany (unifyMany [freshTyVar] declaredArgs [t1,t2]) declaredArgs
      [ue1,ue2] = mUpMany instantArgs [t1,t2] [e1,e2]
  pure ([hs|((<=) <$!> $ue1 <*> $ue2)|], ABS.TSimple $ ABS.U_ $ ABS.U ((0,0),"Bool"))
tStmExp (ABS.EGt l r)   = do
  (e1,t1) <- tStmExp l
  (e2,t2) <- tStmExp r
  let freshTyVar = ABS.U ((0,0),"A'")
      declaredArgs = [ABS.TSimple (ABS.U_ freshTyVar), ABS.TSimple (ABS.U_ freshTyVar)]
      instantArgs = instantiateMany (unifyMany [freshTyVar] declaredArgs [t1,t2]) declaredArgs
      [ue1,ue2] = mUpMany instantArgs [t1,t2] [e1,e2]
  pure ([hs|((>) <$!> $ue1 <*> $ue2)|], ABS.TSimple $ ABS.U_ $ ABS.U ((0,0),"Bool"))
tStmExp (ABS.EGe l r)   = do
  (e1,t1) <- tStmExp l
  (e2,t2) <- tStmExp r
  let freshTyVar = ABS.U ((0,0),"A'")
      declaredArgs = [ABS.TSimple (ABS.U_ freshTyVar), ABS.TSimple (ABS.U_ freshTyVar)]
      instantArgs = instantiateMany (unifyMany [freshTyVar] declaredArgs [t1,t2]) declaredArgs
      [ue1,ue2] = mUpMany instantArgs [t1,t2] [e1,e2]
  pure ([hs|((>=) <$!> $ue1 <*> $ue2)|], ABS.TSimple $ ABS.U_ $ ABS.U ((0,0),"Bool"))
tStmExp (ABS.EAdd l r)  = do 
  (e1,t1) <- tStmExp l
  (e2,t2) <- tStmExp r
  let freshTyVar = ABS.U ((0,0),"A'")
      declaredArgs = [ABS.TSimple (ABS.U_ freshTyVar), ABS.TSimple (ABS.U_ freshTyVar)]
      bs = unifyMany [freshTyVar] declaredArgs [t1,t2]
      instantArgs = instantiateMany bs declaredArgs
      instantRes = instantiateOne bs $ ABS.TSimple (ABS.U_ freshTyVar)
      [ue1,ue2] = mUpMany instantArgs [t1,t2] [e1,e2]
  pure ([hs|((+) <$!> $ue1 <*> $ue2)|], instantRes)
tStmExp (ABS.ESub l r)  = do 
  (e1,t1) <- tStmExp l
  (e2,t2) <- tStmExp r
  let freshTyVar = ABS.U ((0,0),"A'")
      declaredArgs = [ABS.TSimple (ABS.U_ freshTyVar), ABS.TSimple (ABS.U_ freshTyVar)]
      bs = unifyMany [freshTyVar] declaredArgs [t1,t2]
      instantArgs = instantiateMany bs declaredArgs
      instantRes = instantiateOne bs $ ABS.TSimple (ABS.U_ freshTyVar)
      [ue1,ue2] = mUpMany instantArgs [t1,t2] [e1,e2]
  pure ([hs|((-) <$!> $ue1 <*> $ue2)|], instantRes)
tStmExp (ABS.EMul l r)  = do 
  (e1,t1) <- tStmExp l
  (e2,t2) <- tStmExp r
  let freshTyVar = ABS.U ((0,0),"A'")
      declaredArgs = [ABS.TSimple (ABS.U_ freshTyVar), ABS.TSimple (ABS.U_ freshTyVar)]
      bs = unifyMany [freshTyVar] declaredArgs [t1,t2]
      instantArgs = instantiateMany bs declaredArgs
      instantRes = instantiateOne bs $ ABS.TSimple (ABS.U_ freshTyVar)
      [ue1,ue2] = mUpMany instantArgs [t1,t2] [e1,e2]
  pure ([hs|((*) <$!> $ue1 <*> $ue2)|], instantRes)
tStmExp (ABS.EDiv l r)  = do 
  (e1,t1) <- tStmExp l
  (e2,t2) <- tStmExp r
  let declaredArgs = [ABS.TSimple $ ABS.U_ $ ABS.U ((0,0),"Rat"), ABS.TSimple $ ABS.U_ $ ABS.U ((0,0),"Rat")]
      [ue1,ue2] = mUpMany declaredArgs [t1,t2] [e1,e2]
  pure ([hs|((/) <$!> $ue1 <*> $ue2)|], ABS.TSimple $ ABS.U_ $ ABS.U ((0,0),"Rat"))
tStmExp (ABS.EMod l r)  = do 
  (e1,t1) <- tStmExp l
  (e2,t2) <- tStmExp r
  let declaredArgs = [ABS.TSimple $ ABS.U_ $ ABS.U ((0,0),"Rat"), ABS.TSimple $ ABS.U_ $ ABS.U ((0,0),"Rat")]
      [ue1,ue2] = mUpMany declaredArgs [t1,t2] [e1,e2]
  pure ([hs|((%) <$!> $ue1 <*> $ue2)|], ABS.TSimple $ ABS.U_ $ ABS.U ((0,0),"Int"))
tStmExp (ABS.ELogNeg e) = do (te,_) <- tStmExp e; pure ([hs|(not <$!> $te)|], ABS.TSimple $ ABS.U_ $ ABS.U ((0,0),"Bool"))
tStmExp (ABS.EIntNeg e) = do (te,t) <- tStmExp e; pure ([hs|(I'.negate <$!> $te)|], t)

tStmExp (ABS.ESinglConstr (ABS.U_ (ABS.U (_,"Unit"))))     = pure ([hs|I'.pure ()|], ABS.TSimple $ ABS.U_ $ ABS.U ((0,0),"Unit"))
tStmExp (ABS.ESinglConstr (ABS.U_ (ABS.U (_,"Nil"))))      = pure ([hs|I'.pure []|], ABS.TPoly (ABS.U_ $ ABS.U ((0,0), "List")) [ABS.TInfer])
tStmExp (ABS.ESinglConstr (ABS.U_ (ABS.U (_,"EmptyMap")))) = pure ([hs|I'.pure _emptyMap|], ABS.TPoly (ABS.U_ $ ABS.U ((0,0), "Map")) [ABS.TInfer,ABS.TInfer])
tStmExp (ABS.ESinglConstr (ABS.U_ (ABS.U (_,"EmptySet")))) = pure ([hs|I'.pure _emptySet|], ABS.TPoly (ABS.U_ $ ABS.U ((0,0), "Set")) [ABS.TInfer])
tStmExp (ABS.ESinglConstr qu) = tStmExp (ABS.EParamConstr qu [])

-- tStmExp (ABS.ESinglConstr qu) = pure ([hs|I'.pure $(maybeUpException $ HS.Con $ HS.UnQual $ HS.Ident $ showQU qu)|], undefined)
--   where (modul,ident) = splitQU qu
--         maybeUpException = if null modul
--                            then case find (\ (SN ident' modul',_) -> ident == ident' && maybe True (not . snd) modul') (M.assocs ?st) of
--                                   Just (_,SV Exception _) -> HS.Paren . HS.App [hs|I'.toException|]
--                                   _ -> id
--                            else case M.lookup (SN ident (Just (modul, True))) ?st of
--                                   Just (SV Exception _) -> HS.Paren . HS.App [hs|I'.toException|]
--                                   _ -> id

tStmExp (ABS.EParamConstr (ABS.U_ (ABS.U (p,"Triple"))) pexps) =   
    if length pexps == 3
    then do
      ([e1,e2,e3],types) <- unzip <$> mapM tStmExp pexps
      
      pure ([hs|((,,) <$!> $e1 <*> $e2 <*> $e3)|], ABS.TPoly (ABS.U_ (ABS.U ((0,0), "Triple"))) types)
    else errorPos p "wrong number of arguments to Triple"
tStmExp (ABS.EParamConstr (ABS.U_ (ABS.U (p,"Pair"))) pexps) = 
    if length pexps == 2
    then do
      ([e1,e2],types) <- unzip <$> mapM tStmExp pexps
      pure ([hs|((,) <$!> $e1 <*> $e2)|], ABS.TPoly (ABS.U_ (ABS.U ((0,0), "Pair"))) types)
    else errorPos p "wrong number of arguments to Pair"
tStmExp (ABS.EParamConstr (ABS.U_ (ABS.U (_,"Cons"))) [l, r]) = do
   (e1,t1) <- tStmExp l
   (e2,t2) <- tStmExp r
   let freshTyVar = ABS.U ((0,0),"A'");
       declaredArgs = [ABS.TSimple (ABS.U_ freshTyVar), ABS.TPoly (ABS.U_ (ABS.U ((0,0),"List"))) [ABS.TSimple (ABS.U_ freshTyVar)]]
       bs = unifyMany [freshTyVar] declaredArgs [t1,t2]
       instantArgs = instantiateMany bs declaredArgs
       instantRes = instantiateOne bs $ ABS.TPoly (ABS.U_ (ABS.U ((0,0),"List"))) [ABS.TSimple (ABS.U_ freshTyVar)]
       [ue1,ue2] = mUpMany instantArgs [t1,t2] [e1,e2]
   pure ([hs|((:) <$!> $ue1 <*> $ue2)|], instantRes)
tStmExp (ABS.EParamConstr (ABS.U_ (ABS.U (p,"Cons"))) _) = errorPos p "wrong number of arguments to Cons"
tStmExp (ABS.EParamConstr (ABS.U_ (ABS.U (_,"InsertAssoc"))) [l, r]) = do
  (tl,_) <- tStmExp l
  (tr,_) <- tStmExp r
  pure ([hs|(insertAssoc <$!> $tl <*> $tr)|], undefined)
tStmExp (ABS.EParamConstr (ABS.U_ (ABS.U (p,"InsertAssoc"))) _) = errorPos p "wrong number of arguments to InsertAssoc"
tStmExp (ABS.EParamConstr qu args) = do
  let ABS.U_ (ABS.U (_,constrName))= qu
  (es,ts) <- unzip <$> mapM tStmExp args
  case M.lookup (SN constrName Nothing) ?st of
    Just (SV (Datacons _ tyvars declaredArgs declaredRes) _) -> do
      let bs = unifyMany tyvars declaredArgs ts
          instantArgs = instantiateMany bs declaredArgs
          instantRes = instantiateOne bs declaredRes
          es' = mUpMany instantArgs ts es
      pure (HS.Paren $ foldl (\ acc arg -> [hs|$acc <*> $arg|])
                             [hs| I'.pure $(HS.Var $ HS.UnQual $ HS.Ident constrName)|]
                             es', instantRes)          
    _ -> error $ "cannot find constructor " ++ constrName


  -- (\x -> (x,undefined)) .  maybeUpException . HS.Paren <$>
  --   foldlM
  --   (\ acc nextArg -> tStmExp nextArg >>= \ (targ,_) -> pure [hs|$acc <*> $targ|])
  --   [hs|I'.pure $(HS.Con $ HS.UnQual $ HS.Ident $ showQU qu)|]
  --   args
  -- where (modul,ident) = splitQU qu
  --       maybeUpException = if null modul
  --                          then case find (\ (SN ident' modul',_) -> ident == ident' && maybe True (not . snd) modul') (M.assocs ?st) of
  --                                 Just (_,SV Exception _) -> HS.Paren . HS.InfixApp [hs|I'.toException|] (HS.QConOp $ HS.UnQual $ HS.Symbol "<$!>")
  --                                 _ -> id
  --                          else case M.lookup (SN ident (Just (modul, True))) ?st of
  --                                 Just (SV Exception _) -> HS.Paren . HS.InfixApp [hs|I'.toException|] (HS.QConOp $ HS.UnQual $ HS.Symbol "<$!>")
  --                                 _ -> id
                                 
tStmExp (ABS.EVar var@(ABS.L (p,pid))) = do
     scope <- ask
     pure $ case M.lookup var scope of
              Just t -> ([hs|I'.pure $(HS.Var $ HS.UnQual $ HS.Ident pid)|], t)
              Nothing -> case M.lookup var ?vars of
                          Just t -> ([hs|I'.readIORef $(HS.Var $ HS.UnQual $ HS.Ident pid)|], t)
                          Nothing -> case M.lookup var ?fields of
                                    Just t -> let fieldFun = HS.Var $ HS.UnQual $ HS.Ident $ pid ++ "'" ++ ?cname -- accessor
                                              in ([hs|I'.pure ($fieldFun this'')|], t)
                                    Nothing-> case find (\ (SN ident' modul,_) -> pid == ident' && maybe False (not . snd) modul) (M.assocs ?st) of
                                               Just (_,SV Foreign _) -> (HS.Var $ HS.UnQual $ HS.Ident pid, ABS.TInfer)
                                               _ ->  ([hs|I'.pure $(HS.Var $ HS.UnQual $ HS.Ident pid)|], ABS.TInfer) -- errorPos p $ pid ++ " not in scope" --  -- 


tStmExp (ABS.EField var@(ABS.L (p, field))) = if null ?cname
                                                  then error "cannot access fields inside main block"
                                                  else case M.lookup var ?fields of
                                                         Just t -> let fieldFun = HS.Var $ HS.UnQual $ HS.Ident $ field ++ "'" ++ ?cname
                                                                  in pure ([hs|I'.pure ($fieldFun this'')|], t)
                                                         Nothing -> errorPos p "no such field"

tStmExp (ABS.ELit lit) = pure $ case lit of
                                   ABS.LStr str -> ([hs|I'.pure $(HS.Lit $ HS.String str)|], ABS.TSimple $ ABS.U_ $ ABS.U ((0,0),"String"))
                                   ABS.LInt i ->  ([hs|I'.pure $(HS.Lit $ HS.Int i)|], ABS.TInfer)
                                   ABS.LThis -> if null ?cname
                                               then error "cannot access this keyword inside main block"
                                               else ([hs|I'.pure (up' this)|], ABS.TInfer)
                                   ABS.LNull -> ([hs|I'.pure (up' null)|], ABS.TInfer)

mUpOne :: (?st :: SymbolTable) => ABS.T -> ABS.T -> HS.Exp -> HS.Exp
mUpOne unified actual exp = maybe exp (\ info -> HS.ExpTypeSig noLoc' [hs|( $(buildUp info) <$!> $exp )|] (HS.TyApp (HS.TyWildCard Nothing) (tType unified))) (buildInfo unified actual)

mUpMany :: (?st :: SymbolTable) => [ABS.T] -> [ABS.T] -> [HS.Exp] -> [HS.Exp]
mUpMany = zipWith3 mUpOne
  