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
import Language.Haskell.Exts.QQ (hs, ty)
import Data.Foldable (foldlM)
import Data.List (find)

-- | Translating the body of a pure function
tFunBody :: (?st::SymbolTable, ?tyvars::[ABS.U], ?fields::ScopeLVL, ?cname::String)
         => ABS.FunBody -> [ABS.FormalPar] -> HS.Exp
tFunBody ABS.BuiltinFunBody _params = [hs|I'.error "builtin called"|] -- builtin becomes error
tFunBody (ABS.NormalFunBody pexp) params = fst $ runReader (tPureExp pexp) 
                                           (M.fromList $ map (\ (ABS.FormalPar t i) -> (i,t)) params) -- initial function scope is the formal params

-- | Translating a pure expression
tPureExp :: ( ?st::SymbolTable, ?tyvars::[ABS.U], ?fields::ScopeLVL, ?cname::String) 
         => ABS.PureExp -> LetScope (HS.Exp, ABS.T)

tPureExp (ABS.EIf predE thenE elseE) = do
  (ep,_) <- tPureExp predE
  (e1,t1) <- tPureExp thenE
  (e2,t2) <- tPureExp elseE
  let freshTyVar = ABS.U ((0,0),"A'")
      declaredArgs = [ABS.TSimple (ABS.U_ freshTyVar), ABS.TSimple (ABS.U_ freshTyVar)]
      bs = unifyMany [freshTyVar] declaredArgs [t1,t2]
      instantArgs = instantiateMany bs declaredArgs
      instantRes = instantiateOne bs $ ABS.TSimple (ABS.U_ freshTyVar)
      [ue1,ue2] = mUpMany instantArgs [t1,t2] [e1,e2]
  pure ([hs|if $ep then $ue1 else $ue2|], instantRes)

tPureExp (ABS.ELet (ABS.FormalPar ptyp pid@(ABS.L (_,var))) eqE inE) = do
  (tin,_) <- local (M.insert pid ptyp) $ tPureExp inE -- adds to scope
  (teq,_) <- tPureExp eqE
  let pat = HS.Ident var
  pure (case ptyp of
             ABS.TInfer -> [hs|(\ ((pat)) -> $tin) $teq|] -- don't add type-sig, infer it
             _ -> let typ = tTypeOrTyVar ?tyvars ptyp
                 in [hs|(\ ((pat)) -> $tin) ( $teq :: ((typ)) )|]  -- maps to a haskell lambda exp
         ,ptyp)

tPureExp (ABS.ECase ofE branches) = do
  (tof,_) <- tPureExp ofE
  texp <- HS.Case tof <$>
    mapM (\ (ABS.ECaseBranch pat pexp) -> do
            (texp,_) <- tPureExp pexp
            (tpat,tguards) <- tPattern pat
            pure $ HS.Alt noLoc' tpat ((if null tguards then HS.UnGuardedRhs else (HS.GuardedRhss . pure . HS.GuardedRhs noLoc' tguards)) texp) Nothing
         ) branches
  pure (texp, undefined)

tPureExp (ABS.EFunCall ql args) = do
  (es,ts) <- unzip <$> mapM tPureExp args
  let ABS.L_ (ABS.L (_,funName))= ql
  case M.lookup (SN funName Nothing) ?st of
    Just (SV (Function tyvars declaredArgs declaredRes) _) -> do
      let bs = unifyMany tyvars declaredArgs ts
          instantArgs = instantiateMany bs declaredArgs
          instantRes = instantiateOne bs declaredRes
          es' = mUpMany instantArgs ts es
      pure (HS.Paren $ foldl HS.App
                          (HS.Var $ HS.UnQual $ HS.Ident $ showQL ql)
                          es', instantRes)          
    _ -> error $ "cannot find function " ++ funName

tPureExp (ABS.ENaryFunCall ql args) = do
  (es,ts) <- unzip <$> mapM tPureExp args
  let ABS.L_ (ABS.L (_,funName))= ql
  case M.lookup (SN funName Nothing) ?st of
    Just (SV (Function tyvars declaredArgs declaredRes) _) -> do
      let bs = unifyMany tyvars declaredArgs ts
          instantArgs = instantiateMany bs declaredArgs
          instantRes = instantiateOne bs declaredRes
          es' = mUpMany instantArgs ts es
      pure (HS.Paren $ HS.App
                        (HS.Var $ HS.UnQual $ HS.Ident $ showQL ql)
                        (HS.List es')
           , instantRes)          
    _ -> error $ "cannot find function " ++ funName


-- constants
tPureExp (ABS.EEq (ABS.ELit ABS.LNull) (ABS.ELit ABS.LNull)) = pure ([hs|True|], ABS.TSimple $ ABS.U_ $ ABS.U ((0,0),"Bool"))
tPureExp (ABS.EEq (ABS.ELit ABS.LThis) (ABS.ELit ABS.LThis)) = pure ([hs|True|], ABS.TSimple $ ABS.U_ $ ABS.U ((0,0),"Bool"))
tPureExp (ABS.EEq (ABS.ELit ABS.LNull) (ABS.ELit ABS.LThis)) = pure ([hs|False|], ABS.TSimple $ ABS.U_ $ ABS.U ((0,0),"Bool"))

-- optimization, to wrap null with the direct interface of rhs instead of up'
tPureExp (ABS.EEq (ABS.ELit ABS.LNull) pvar@(ABS.EVar ident@(ABS.L (p,str)))) = do
   scope <- ask
   (tvar,_) <- tPureExp pvar
   pure $ case M.lookup ident (scope `M.union` ?fields) of -- check the type of the right var
            Just (ABS.TSimple qu) -> ([hs|( $(HS.Var $ HS.UnQual $ HS.Ident $ showQU qu) null == $tvar )|], ABS.TSimple $ ABS.U_ $ ABS.U ((0,0),"Bool"))
            Just _ -> errorPos p "cannot equate null to non-interface type"
            Nothing -> errorPos p $ str ++ " variable not in scope or has foreign type"
-- commutative
tPureExp (ABS.EEq pvar@(ABS.EVar _) pnull@(ABS.ELit ABS.LNull)) = tPureExp (ABS.EEq pnull pvar)

-- optimization, to wrap null with the direct interface of rhs instead of up'
tPureExp (ABS.EEq (ABS.ELit ABS.LNull) pvar@(ABS.EField ident@(ABS.L (p,str)))) = do
   (tvar,_) <- tPureExp pvar
   pure $ case M.lookup ident ?fields of -- check the type of the right var
            Just (ABS.TSimple qu) -> ([hs|( $(HS.Var $ HS.UnQual $ HS.Ident $ showQU qu) null == $tvar )|], ABS.TSimple $ ABS.U_ $ ABS.U ((0,0),"Bool"))
            Just _ -> errorPos p "cannot equate null to non-interface type"
            Nothing -> errorPos p $ str ++ " not in scope"
-- commutative
tPureExp (ABS.EEq pvar@(ABS.EField _) pnull@(ABS.ELit ABS.LNull)) = tPureExp (ABS.EEq pnull pvar)

-- a catch-all for literals,constructors,vars
tPureExp (ABS.EEq l r) = do 
  (e1,t1) <- tPureExp l
  (e2,t2) <- tPureExp r;
  let freshTyVar = ABS.U ((0,0),"A'")
      declaredArgs = [ABS.TSimple (ABS.U_ freshTyVar), ABS.TSimple (ABS.U_ freshTyVar)]
      instantArgs = instantiateMany (unifyMany [freshTyVar] declaredArgs [t1,t2]) declaredArgs
      [ue1,ue2] = mUpMany instantArgs [t1,t2] [e1,e2]
  pure ([hs|($ue1 == $ue2)|], ABS.TSimple $ ABS.U_ $ ABS.U ((0,0),"Bool"))

-- -- normalizess to not . ==
tPureExp (ABS.ENeq left right) = tPureExp (ABS.ELogNeg $ ABS.EEq left right) 

-- -- be careful to parenthesize infix apps
tPureExp (ABS.EOr l r)   = do (tl,_) <- tPureExp l;  (tr,_) <- tPureExp r; pure ([hs|($tl || $tr)|], ABS.TSimple $ ABS.U_ $ ABS.U ((0,0),"Bool"))
tPureExp (ABS.EAnd l r)  = do (tl,_) <- tPureExp l;  (tr,_) <- tPureExp r; pure ([hs|($tl && $tr)|], ABS.TSimple $ ABS.U_ $ ABS.U ((0,0),"Bool"))
tPureExp (ABS.ELt l r)   = do 
  (e1,t1) <- tPureExp l
  (e2,t2) <- tPureExp r
  let freshTyVar = ABS.U ((0,0),"A'")
      declaredArgs = [ABS.TSimple (ABS.U_ freshTyVar), ABS.TSimple (ABS.U_ freshTyVar)]
      instantArgs = instantiateMany (unifyMany [freshTyVar] declaredArgs [t1,t2]) declaredArgs
      [ue1,ue2] = mUpMany instantArgs [t1,t2] [e1,e2]
  pure ([hs|($ue1 < $ue2)|], ABS.TSimple $ ABS.U_ $ ABS.U ((0,0),"Bool"))

tPureExp (ABS.ELe l r)   = do 
  (e1,t1) <- tPureExp l
  (e2,t2) <- tPureExp r
  let freshTyVar = ABS.U ((0,0),"A'")
      declaredArgs = [ABS.TSimple (ABS.U_ freshTyVar), ABS.TSimple (ABS.U_ freshTyVar)]
      instantArgs = instantiateMany (unifyMany [freshTyVar] declaredArgs [t1,t2]) declaredArgs
      [ue1,ue2] = mUpMany instantArgs [t1,t2] [e1,e2]
  pure ([hs|($ue1 <= $ue2)|], ABS.TSimple $ ABS.U_ $ ABS.U ((0,0),"Bool"))
tPureExp (ABS.EGt l r)   = do 
  (e1,t1) <- tPureExp l
  (e2,t2) <- tPureExp r
  let freshTyVar = ABS.U ((0,0),"A'")
      declaredArgs = [ABS.TSimple (ABS.U_ freshTyVar), ABS.TSimple (ABS.U_ freshTyVar)]
      instantArgs = instantiateMany (unifyMany [freshTyVar] declaredArgs [t1,t2]) declaredArgs
      [ue1,ue2] = mUpMany instantArgs [t1,t2] [e1,e2]
  pure ([hs|($ue1 > $ue2)|], ABS.TSimple $ ABS.U_ $ ABS.U ((0,0),"Bool"))
tPureExp (ABS.EGe l r)   = do 
  (e1,t1) <- tPureExp l
  (e2,t2) <- tPureExp r
  let freshTyVar = ABS.U ((0,0),"A'")
      declaredArgs = [ABS.TSimple (ABS.U_ freshTyVar), ABS.TSimple (ABS.U_ freshTyVar)]
      instantArgs = instantiateMany (unifyMany [freshTyVar] declaredArgs [t1,t2]) declaredArgs
      [ue1,ue2] = mUpMany instantArgs [t1,t2] [e1,e2]
  pure ([hs|($ue1 >= $ue2)|], ABS.TSimple $ ABS.U_ $ ABS.U ((0,0),"Bool"))
tPureExp (ABS.EAdd l r)  = do
  (e1,t1) <- tPureExp l
  (e2,t2) <- tPureExp r
  let freshTyVar = ABS.U ((0,0),"A'")
      declaredArgs = [ABS.TSimple (ABS.U_ freshTyVar), ABS.TSimple (ABS.U_ freshTyVar)]
      bs = unifyMany [freshTyVar] declaredArgs [t1,t2]
      instantArgs = instantiateMany bs declaredArgs
      instantRes = instantiateOne bs $ ABS.TSimple (ABS.U_ freshTyVar)
      [ue1,ue2] = mUpMany instantArgs [t1,t2] [e1,e2]
  pure ([hs|($ue1 + $ue2)|], instantRes)
tPureExp (ABS.ESub l r)  =  do
  (e1,t1) <- tPureExp l
  (e2,t2) <- tPureExp r
  let freshTyVar = ABS.U ((0,0),"A'")
      declaredArgs = [ABS.TSimple (ABS.U_ freshTyVar), ABS.TSimple (ABS.U_ freshTyVar)]
      bs = unifyMany [freshTyVar] declaredArgs [t1,t2]
      instantArgs = instantiateMany bs declaredArgs
      instantRes = instantiateOne bs $ ABS.TSimple (ABS.U_ freshTyVar)
      [ue1,ue2] = mUpMany instantArgs [t1,t2] [e1,e2]
  pure ([hs|($ue1 - $ue2)|], instantRes)
tPureExp (ABS.EMul l r)  = do
  (e1,t1) <- tPureExp l
  (e2,t2) <- tPureExp r
  let freshTyVar = ABS.U ((0,0),"A'")
      declaredArgs = [ABS.TSimple (ABS.U_ freshTyVar), ABS.TSimple (ABS.U_ freshTyVar)]
      bs = unifyMany [freshTyVar] declaredArgs [t1,t2]
      instantArgs = instantiateMany bs declaredArgs
      instantRes = instantiateOne bs $ ABS.TSimple (ABS.U_ freshTyVar)
      [ue1,ue2] = mUpMany instantArgs [t1,t2] [e1,e2]
  pure ([hs|($ue1 * $ue2)|], instantRes)
tPureExp (ABS.EDiv l r)  = do 
  (e1,t1) <- tPureExp l
  (e2,t2) <- tPureExp r
  let freshTyVar = ABS.U ((0,0),"A'")
      declaredArgs = [ABS.TSimple (ABS.U_ freshTyVar), ABS.TSimple (ABS.U_ freshTyVar)]
      instantArgs = instantiateMany (unifyMany [freshTyVar] declaredArgs [t1,t2]) declaredArgs
      [ue1,ue2] = mUpMany instantArgs [t1,t2] [e1,e2]
  pure ([hs|($ue1 / $ue2)|], ABS.TSimple $ ABS.U_ $ ABS.U ((0,0),"Rat"))
tPureExp (ABS.EMod l r)  = do
  (e1,t1) <- tPureExp l
  (e2,t2) <- tPureExp r
  let declaredArgs = [ABS.TSimple $ ABS.U_ $ ABS.U ((0,0),"Rat"), ABS.TSimple $ ABS.U_ $ ABS.U ((0,0),"Rat")]
      [ue1,ue2] = mUpMany declaredArgs [t1,t2] [e1,e2]
  pure ([hs|($ue1 % $ue2)|], ABS.TSimple $ ABS.U_ $ ABS.U ((0,0),"Int"))

tPureExp (ABS.ELogNeg e) = do (te,_) <- tPureExp e; pure ([hs|(not $te)|], ABS.TSimple $ ABS.U_ $ ABS.U ((0,0),"Bool"))
tPureExp (ABS.EIntNeg e) = do (te,t) <- tPureExp e; pure ([hs|(- $te)|], t)

tPureExp (ABS.ESinglConstr (ABS.U_ (ABS.U (_,"Unit"))))     = pure ([hs|()|], ABS.TSimple $ ABS.U_ $ ABS.U ((0,0),"Unit"))
tPureExp (ABS.ESinglConstr (ABS.U_ (ABS.U (_,"Nil"))))      = pure ([hs|[]|], ABS.TPoly (ABS.U_ $ ABS.U ((0,0), "List")) [ABS.TInfer])
tPureExp (ABS.ESinglConstr (ABS.U_ (ABS.U (_,"EmptyMap")))) = pure ([hs|_emptyMap|], ABS.TPoly (ABS.U_ $ ABS.U ((0,0), "Map")) [ABS.TInfer,ABS.TInfer])
tPureExp (ABS.ESinglConstr (ABS.U_ (ABS.U (_,"EmptySet")))) = pure ([hs|_emptySet|], ABS.TPoly (ABS.U_ $ ABS.U ((0,0), "Set")) [ABS.TInfer])
tPureExp (ABS.ESinglConstr qu) = tPureExp (ABS.EParamConstr qu [])


  -- pure $ (maybeUpException $ HS.Con $ HS.UnQual $ HS.Ident $ showQU qu, undefined)
  -- where (modul,ident) = splitQU qu
  --       maybeUpException = if null modul
  --                          then case find (\ (SN ident' modul',_) -> ident == ident' && maybe True (not . snd) modul') (M.assocs ?st) of
  --                                 Just (_,SV Exception _) -> HS.Paren . HS.App [hs|I'.toException|]
  --                                 _ -> id
  --                          else case M.lookup (SN ident (Just (modul, True))) ?st of
  --                                 Just (SV Exception _) -> HS.Paren . HS.App [hs|I'.toException|]
  --                                 _ -> id
                          
tPureExp (ABS.EParamConstr (ABS.U_ (ABS.U (p,"Triple"))) pexps) =   
    if length pexps == 3
    then do
      (texps,types) <- unzip <$> mapM tPureExp pexps
      pure (HS.Paren $ HS.Tuple HS.Boxed texps, ABS.TPoly (ABS.U_ (ABS.U ((0,0), "Triple"))) types)
    else errorPos p "wrong number of arguments to Triple"
tPureExp (ABS.EParamConstr (ABS.U_ (ABS.U (p,"Pair"))) pexps) = 
    if length pexps == 2
    then do
      (texps,types) <- unzip <$> mapM tPureExp pexps
      pure (HS.Paren $ HS.Tuple HS.Boxed texps, ABS.TPoly (ABS.U_ (ABS.U ((0,0), "Pair"))) types)
    else errorPos p "wrong number of arguments to Pair"
tPureExp (ABS.EParamConstr (ABS.U_ (ABS.U (_,"Cons"))) [l, r]) = do
   (e1,t1) <- tPureExp l
   (e2,t2) <- tPureExp r
   let freshTyVar = ABS.U ((0,0),"A'");
       declaredArgs = [ABS.TSimple (ABS.U_ freshTyVar), ABS.TPoly (ABS.U_ (ABS.U ((0,0),"List"))) [ABS.TSimple (ABS.U_ freshTyVar)]]
       bs = unifyMany [freshTyVar] declaredArgs [t1,t2]
       instantArgs = instantiateMany bs declaredArgs
       instantRes = instantiateOne bs $ ABS.TPoly (ABS.U_ (ABS.U ((0,0),"List"))) [ABS.TSimple (ABS.U_ freshTyVar)]
       [ue1,ue2] = mUpMany instantArgs [t1,t2] [e1,e2]
   pure ([hs|($ue1 : $ue2)|], instantRes)

tPureExp (ABS.EParamConstr (ABS.U_ (ABS.U (p,"Cons"))) _) = errorPos p "wrong number of arguments to Cons"
tPureExp (ABS.EParamConstr (ABS.U_ (ABS.U (_,"InsertAssoc"))) [l, r]) = do
  (tl,_) <- tPureExp l
  (tr,_) <- tPureExp r
  pure ([hs|(insertAssoc $tl $tr)|], undefined)
tPureExp (ABS.EParamConstr (ABS.U_ (ABS.U (p,"InsertAssoc"))) _) = errorPos p "wrong number of arguments to InsertAssoc"
tPureExp (ABS.EParamConstr qu args) = do
  let ABS.U_ (ABS.U (_,constrName))= qu
  (es,ts) <- unzip <$> mapM tPureExp args
  case M.lookup (SN constrName Nothing) ?st of
    Just (SV (Datacons _ tyvars declaredArgs declaredRes) _) -> do
      let bs = unifyMany tyvars declaredArgs ts
          instantArgs = instantiateMany bs declaredArgs
          instantRes = instantiateOne bs declaredRes
          es' = mUpMany instantArgs ts es
      pure (HS.Paren $ foldl HS.App
                          (HS.Var $ HS.UnQual $ HS.Ident $ showQU qu)
                          es', instantRes)          
    _ -> error $ "cannot find constructor " ++ constrName

  -- texp <- maybeUpException . HS.Paren <$>
  --                                       foldlM (\ acc nextArg -> HS.App acc . fst <$> tPureExp nextArg)
  --                                       (HS.Con $ HS.UnQual $ HS.Ident $ showQU qu)
  --                                       args
  -- pure (texp, undefined)
  -- where (modul,ident) = splitQU qu
  --       maybeUpException = if null modul
  --                          then case find (\ (SN ident' modul',_) -> ident == ident' && maybe True (not . snd) modul') (M.assocs ?st) of
  --                                 Just (_,SV Exception _) -> HS.Paren . HS.App [hs|I'.toException|]
  --                                 _ -> id
  --                          else case M.lookup (SN ident (Just (modul, True))) ?st of
  --                                 Just (SV Exception _) -> HS.Paren . HS.App [hs|I'.toException|]
  --                                 _ -> id
    
tPureExp (ABS.EVar var@(ABS.L (p,pid))) = do
     scope <- ask
     pure $ case M.lookup var scope of
              Just t -> (HS.Var $ HS.UnQual $ HS.Ident pid, t)
              Nothing ->  case M.lookup var ?fields of
                           Just t -> if null ?cname
                                    then (HS.Var $ HS.UnQual $ HS.Ident $ pid ++ "'this", t) -- errorPos p "cannot access fields inside main block or pure functions"
                                    else let fieldFun = HS.Var $ HS.UnQual $ HS.Ident $ pid ++ "'" ++ ?cname -- accessor
                                         in ([hs|($fieldFun this'')|], t) -- accessor
                           Nothing -> case find (\ (SN ident' modul,_) -> pid == ident' && maybe False (not . snd) modul) (M.assocs ?st) of
                                       Just (_,SV Foreign _) -> (HS.Var $ HS.UnQual $ HS.Ident pid, ABS.TInfer)
                                       _ ->  (HS.Var $ HS.UnQual $ HS.Ident pid, ABS.TInfer) -- errorPos p $ pid ++ " not in scope" -- 


tPureExp (ABS.EField var@(ABS.L (p, field))) = case M.lookup var ?fields of
                                                  Just t -> pure $ if null ?cname
                                                            then (HS.Var $ HS.UnQual $ HS.Ident $ field ++ "'this", t) -- errorPos p "cannot access fields inside main block or pure code"
                                                            else let fieldFun = HS.Var $ HS.UnQual $ HS.Ident $ field ++ "'" ++ ?cname
                                                                 in ([hs|($fieldFun this'')|], t)
                                                  Nothing -> errorPos p "no such field"
  
tPureExp (ABS.ELit lit) = pure $ case lit of
                                   ABS.LStr str -> (HS.Lit $ HS.String str, ABS.TSimple $ ABS.U_ $ ABS.U ((0,0),"String"))
                                   ABS.LInt i -> (HS.Lit $ HS.Int i, ABS.TInfer)
                                   --(HS.ExpTypeSig noLoc' (HS.Lit $ HS.Int i) [ty|Int|], ABS.TSimple $ ABS.U_ $ ABS.U $ ((0,0),"Int"))
                                   ABS.LThis -> if null ?cname
                                                then error "cannot access this keyword inside main block or pure code"
                                                else ([hs|this|],ABS.TInfer)
                                                  -- case find (\ (SN ident' modul,_) -> ?cname == ident' && maybe False (not . snd) modul) (M.assocs ?st) of
                                                  --     Just (_,SV (Class is) _) -> ([hs|(up' this)|], is) -- Class has a polymorphic type of all directly-implemented interfaces
                                                      -- _ -> error "dev error: cannot find such class"
                                   ABS.LNull -> ([hs|null|], ABS.TInfer)