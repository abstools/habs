{-# LANGUAGE CPP, ImplicitParams, QuasiQuotes #-}
module ABS.Compiler.Codegen.Stm
    ( tMethod
    ) where

import ABS.Compiler.Utils
import ABS.Compiler.Codegen.Base
import ABS.Compiler.Firstpass.Base
import ABS.Compiler.Codegen.Exp (tPureExp)
import ABS.Compiler.Codegen.StmExp (tStmExp)
import ABS.Compiler.Codegen.Typ
import qualified ABS.AST as ABS
import qualified Language.Haskell.Exts.Syntax as HS
import Language.Haskell.Exts.SrcLoc (noLoc)
import Language.Haskell.Exts.QQ (hs)

import Control.Monad.Trans.State (evalState, get, put, modify')
import Control.Monad.Trans.Reader (runReader, ask, local)
import qualified Data.Map as M
import Control.Applicative ((<|>))
import Data.Foldable (foldlM)

import Control.Exception (assert)
#define todo assert False

tMethod :: (?st :: SymbolTable) => ABS.Block -> [ABS.Param] -> M.Map ABS.LIdent ABS.Type -> String -> HS.Exp
tMethod (ABS.Bloc mbody) mparams fields cname = evalState (let ?fields = fields  -- fixed fields passed as an implicit param
                                                               ?cname = cname    -- className needed for field pattern-matching
                                                             in HS.Do . concat <$> mapM tStm mbody)
                                          [M.empty, -- new scope
                                           M.fromList (map (\ (ABS.Par t i) -> (i,t)) mparams)] -- first scope level is the formal params


--- VARIABLE-ASSIGNMENT STATEMENTS
-------------------------

tStm (ABS.AnnStm _ (ABS.SDec t i@(ABS.LIdent (p,n)))) = case t of

  ABS.TGen (ABS.QTyp [ABS.QTypeSegmen (ABS.UIdent (_,"Fut"))])  _ -> do   -- it is an unitialized future (set to newEmptyMVar)
      addToScope t i
      pure [HS.Generator noLoc 
                   (HS.PatTypeSig noLoc (HS.PVar $ HS.Ident n) (HS.TyApp (HS.TyCon $ HS.UnQual $ HS.Ident "IORef'") (tType t)))   -- f :: IORef (Fut a) <- emptyFuture
                   [hs| I'.liftIO (I'.newIORef =<< emptyFuture) |]]

  ABS.TSimple qtyp -> let   -- it may be an object (set to null) or foreign (set to undefined)
                       (prefix, ident) = splitQType qtyp
                       Just (SV symbolType _) = if null prefix
                                                then M.lookup (SN ident Nothing) ?st
                                                else M.lookup (SN ident (Just (prefix, False))) ?st 
                                                           <|> M.lookup (SN ident (Just (prefix, True))) ?st 
                     in case symbolType of
                          Interface _ _ -> do
                                          addToScope t i
                                          pure [HS.Generator noLoc 
                                                      (HS.PatTypeSig noLoc (HS.PVar $ HS.Ident n) (HS.TyApp (HS.TyCon $ HS.UnQual $ HS.Ident "IORef'") (tType t))) -- o :: IORef Interf <- null
                                                      [hs| I'.liftIO (I'.newIORef ($(HS.Var $ HS.UnQual $ HS.Ident $ showQType qtyp) null)) |] ]
                          Foreign -> do
                            addToScope t i
                            pure [HS.Generator noLoc
                                        (HS.PVar $ HS.Ident n) -- no type of foreign object :  foreign <- newIORef undefined
                                        [hs| I'.liftIO (I'.newIORef undefined) |] ]
                          _ -> errorPos p "A field must be initialised if it is not of a reference type"


tStm (ABS.AnnStm _ (ABS.SDecAss t i@(ABS.LIdent (_,n)) (ABS.ExpE eexp))) = do
  addToScope t i
  texp <- tEffExp eexp False -- not standalone
  pure [ HS.Generator noLoc 
               (HS.PatTypeSig noLoc (HS.PVar $ HS.Ident n) (HS.TyApp (HS.TyCon $ HS.UnQual $ HS.Ident "IORef'") (tType t))) $
                 case eexp of
                   ABS.New _ _ -> case t of ABS.TSimple qtyp -> [hs| (I'.liftIO . I'.newIORef . $(HS.Var $ HS.UnQual $ HS.Ident $ showQType qtyp)) =<< $texp |] 
                   ABS.NewLocal _ _ -> case t of ABS.TSimple qtyp -> [hs| (I'.liftIO . I'.newIORef . $(HS.Var $ HS.UnQual $ HS.Ident $ showQType qtyp)) =<< $texp |]
                   _ -> [hs| (I'.liftIO . I'.newIORef) =<< $texp |] 
       ]

tStm (ABS.AnnStm _ (ABS.SDecAss t i@(ABS.LIdent (_,n)) (ABS.ExpP pexp))) = do
  addToScope t i
  (locals, fields) <- depends pexp
  scopeLevels <- get
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
      maybeWrapThis = if null fields then id else (\ e -> [hs| (\ this' -> $e) =<< readIORef this|])
  if null locals
    then do
      let texp = runReader (let ?tyvars = [] in tPureExp pexp) formalParams
      pure [ HS.Generator noLoc 
                   (HS.PatTypeSig noLoc (HS.PVar $ HS.Ident n) (HS.TyApp (HS.TyCon $ HS.UnQual $ HS.Ident "IORef'") (tType t)))
                   $ maybeWrapThis [hs| I'.liftIO (I'.newIORef $texp) |] ]
    else do
      let texp = runReader (let ?vars = localVars in tStmExp pexp) formalParams
      pure [ HS.Generator noLoc 
               (HS.PatTypeSig noLoc (HS.PVar $ HS.Ident n) (HS.TyApp (HS.TyCon $ HS.UnQual $ HS.Ident "IORef'") (tType t)))
               $ maybeWrapThis [hs| I'.liftIO (I'.newIORef =<< $texp) |] ]


tStm (ABS.AnnStm _ (ABS.SAss i@(ABS.LIdent (_,n)) (ABS.ExpE eexp))) = do
  texp <- tEffExp eexp False -- not standalone
  Just t <- M.lookup i . M.unions <$> get
  pure [ HS.Generator noLoc 
               (HS.PVar $ HS.Ident n) $
                 case eexp of
                   ABS.New _ _ -> case t of ABS.TSimple qtyp -> [hs| (I'.liftIO . I'.newIORef . $(HS.Var $ HS.UnQual $ HS.Ident $ showQType qtyp)) =<< $texp |] 
                   ABS.NewLocal _ _ -> case t of ABS.TSimple qtyp -> [hs| (I'.liftIO . I'.newIORef . $(HS.Var $ HS.UnQual $ HS.Ident $ showQType qtyp)) =<< $texp |]
                   _ -> [hs| (I'.liftIO . I'.newIORef) =<< $texp |] 
       ]

tStm (ABS.AnnStm _ (ABS.SAss (ABS.LIdent (_,n)) (ABS.ExpP pexp))) = do
  (locals, fields) <- depends pexp
  scopeLevels <- get
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
      maybeWrapThis = if null fields then id else (\ e -> [hs| (\ this' -> $e) =<< readIORef this|])
  if null locals
    then do
      let texp = runReader (let ?tyvars = [] in tPureExp pexp) formalParams
      pure [ HS.Generator noLoc 
                   (HS.PVar $ HS.Ident n)
                   $ maybeWrapThis [hs| I'.liftIO (I'.newIORef $texp) |] ]
    else do
      let texp = runReader (let ?vars = localVars in tStmExp pexp) formalParams
      pure [ HS.Generator noLoc 
               (HS.PVar $ HS.Ident n)
               $ maybeWrapThis [hs| I'.liftIO (I'.newIORef =<< $texp) |] ]


tStm (ABS.AnnStm _ (ABS.SFieldAss i e)) = todo undefined

-- CONCURRENCY STATEMENTS
-------------------------

tStm (ABS.AnnStm _ ABS.SSuspend) = pure [HS.Qualifier [hs| suspend this |]]

tStm (ABS.AnnStm _ (ABS.SAwait g)) = do
  let (futureGuards, boolGuards) = splitGuard g
  tfguards <- mapM tGuard futureGuards   -- sequentialize: await f1guard? ; await f2guard?;
  tbguards <- if null boolGuards
             then pure []                           
             else tGuard (foldl1 (\ (ABS.ExpGuard exp1) (ABS.ExpGuard exp2) -> ABS.ExpGuard $ exp1 `ABS.EAnd` exp2) boolGuards) -- combine bguards with boolean AND
  pure $ concat tfguards
       ++ tbguards
  where
    splitGuard :: ABS.AwaitGuard -> ([ABS.AwaitGuard], [ABS.AwaitGuard])
    splitGuard g = splitGuard' g ([],[])
    splitGuard' g (fs,as)= case g of
                             ABS.FutFieldGuard _ -> (g:fs,as)
                             ABS.FutGuard _ -> (g:fs,as)
                             ABS.ExpGuard _ -> (fs,g:as)
                             ABS.AndGuard gl gr -> let 
                                                   (fsl,asl) = splitGuard gl
                                                   (fsr,asr) = splitGuard gr 
                                                  in (fsl++fs++fsr,asl++as++asr)

    tGuard (ABS.FutGuard var@(ABS.LIdent (_, fname))) = do
      inScope <- M.member var . M.unions <$> get
      if inScope
        then pure [HS.Qualifier [hs| awaitFuture' =<< $(HS.Var $ HS.UnQual $ HS.Ident fname) |]]
        else tGuard (ABS.FutFieldGuard var) -- try as field-future

    -- currently, no solution to the cosimo problem
    tGuard (ABS.FutFieldGuard (ABS.LIdent (_, fname))) = do
      let fieldFun = HS.Var $ HS.UnQual $ HS.Ident $ fname ++ "'" ++ ?cname
      pure [HS.Qualifier [hs| (awaitFuture' . $fieldFun) =<< I'.liftIO (I'.readIORef this) |]]

    tGuard (ABS.ExpGuard pexp) = do
      pure [HS.Qualifier [hs| awaitBool' TODO |]]

    tGuard _ = error "dev-error: this should not match"

-- CONTROL FLOW STATEMENTS
--------------------------

tStm (ABS.AnnStm _ (ABS.SWhile pexp stmBody)) = do
  scopeLevels <- get
  (_, fields) <- depends pexp
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
      maybeWrapThis = if null fields then id else (\ e -> [hs| (\ this' -> $e) =<< readIORef this|])
  let texp = runReader (let ?vars = localVars in tStmExp pexp) formalParams  -- only treat it as StmExp
  [HS.Qualifier tbody] <- tStm $ ABS.AnnStm [] (ABS.SBlock [stmBody])
  pure $ [HS.Qualifier $ maybeWrapThis [hs| while $texp $tbody |] ]              

tStm (ABS.AnnStm _ (ABS.SIf pexp stmThen)) = do
  scopeLevels <- get
  (locals, fields) <- depends pexp
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
      maybeWrapThis = if null fields then id else (\ e -> [hs| (\ this' -> $e) =<< readIORef this|])
  if null locals
    then do
      let tpred = runReader (let ?tyvars = [] in tPureExp pexp) formalParams
      [HS.Qualifier tthen] <- tStm $ ABS.AnnStm [] (ABS.SBlock [stmThen])
      pure [HS.Qualifier $ maybeWrapThis [hs| when $tpred $tthen |]]
    else do
      let tpred = runReader (let ?vars = localVars in tStmExp pexp) formalParams
      [HS.Qualifier tthen] <- tStm $ ABS.AnnStm [] (ABS.SBlock [stmThen])
      pure [ HS.Generator noLoc (HS.PVar $ HS.Ident "when'") tpred
           , HS.Qualifier $ maybeWrapThis [hs| when when' $tthen |]]

tStm (ABS.AnnStm _ (ABS.SIfElse pexp stmThen stmElse)) = do
  scopeLevels <- get
  (locals, fields) <- depends pexp
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
      maybeWrapThis = if null fields then id else (\ e -> [hs| (\ this' -> $e) =<< readIORef this|])
  if null locals
    then do
      let tpred = runReader (let ?tyvars = [] in tPureExp pexp) formalParams
      [HS.Qualifier tthen] <- tStm $ ABS.AnnStm [] (ABS.SBlock [stmThen])
      [HS.Qualifier telse] <- tStm $ ABS.AnnStm [] (ABS.SBlock [stmElse])
      pure [HS.Qualifier $ maybeWrapThis [hs| if $tpred then $tthen else $telse |]]
    else do
      let tpred = runReader (let ?vars = localVars in tStmExp pexp) formalParams
      [HS.Qualifier tthen] <- tStm $ ABS.AnnStm [] (ABS.SBlock [stmThen])
      [HS.Qualifier telse] <- tStm $ ABS.AnnStm [] (ABS.SBlock [stmElse])
      pure [ HS.Generator noLoc (HS.PVar $ HS.Ident "if'") tpred
           , HS.Qualifier $ maybeWrapThis [hs| if if' then $tthen else $telse |]]

-- CLASSIC IMPERATIVE STATEMENTS
--------------------------------

tStm (ABS.AnnStm a (ABS.SReturn e)) = tStm (ABS.AnnStm a (ABS.SExp e)) -- treat it as a standalone statement

tStm (ABS.AnnStm _ (ABS.SSkip)) = pure [] -- ignore skip

tStm (ABS.AnnStm _ (ABS.SBlock astms)) = do
  modify' (M.empty:)            -- add scope-level
  tstms <- mapM tStm astms
  modify' tail                  -- remove scope-level
  pure [HS.Qualifier $ HS.Do $ concat tstms]

tStm (ABS.AnnStm _ (ABS.SPrint pexp)) = do
  (locals, fields) <- depends pexp
  scopeLevels <- get
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
      maybeWrapThis = if null fields then id else (\ e -> [hs| (\ this' -> $e) =<< readIORef this|])
  if null locals
    then do
      let texp = runReader (let ?tyvars = [] in tPureExp pexp) formalParams
      pure $ [HS.Qualifier $ maybeWrapThis [hs| I'.liftIO (I'.putStrLn $texp) |] ]
    else do
      let texp = runReader (let ?vars = localVars in tStmExp pexp) formalParams
      pure $ [HS.Qualifier $ maybeWrapThis [hs| I'.liftIO (I'.putStrLn =<< $texp) |] ]

tStm (ABS.AnnStm _ (ABS.SExp (ABS.ExpE eexp))) = do
  texp <- tEffExp eexp True -- is a standalone statement
  pure [HS.Qualifier texp]
tStm (ABS.AnnStm _ (ABS.SExp (ABS.ExpP pexp))) = do
  (locals, fields) <- depends pexp
  scopeLevels <- get
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
      maybeWrapThis = if null fields then id else (\ e -> [hs| (\ this' -> $e) =<< readIORef this|])
  if null locals
    then do
      let texp = runReader (let ?tyvars = [] in tPureExp pexp) formalParams
      pure $ [HS.Qualifier $ maybeWrapThis [hs| I'.pure $texp |] ]
    else do
      let texp = runReader (let ?vars = localVars in tStmExp pexp) formalParams
      pure $ [HS.Qualifier $ maybeWrapThis [hs| $texp |] ] -- by itself

-- EXCEPTION STATEMENTS
-------------------------

tStm (ABS.AnnStm _ (ABS.SAssert pexp)) = do
  (locals, fields) <- depends pexp
  scopeLevels <- get
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
      maybeWrapThis = if null fields then id else (\ e -> [hs| (\ this' -> $e) =<< readIORef this|])
  if null locals
    then do
      let texp = runReader (let ?tyvars = [] in tPureExp pexp) formalParams
      pure $ [HS.Qualifier $ maybeWrapThis [hs| assert $texp |] ]
    else do
      let texp = runReader (let ?vars = localVars in tStmExp pexp) formalParams
      pure $ [HS.Qualifier $ maybeWrapThis [hs| assert =<< $texp |] ]

tStm (ABS.AnnStm _ (ABS.SThrow pexp)) = do
  (locals, fields) <- depends pexp
  scopeLevels <- get
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
      maybeWrapThis = if null fields then id else (\ e -> [hs| (\ this' -> $e) =<< readIORef this|])
  if null locals
    then do
      let texp = runReader (let ?tyvars = [] in tPureExp pexp) formalParams
      pure $ [HS.Qualifier $ maybeWrapThis [hs| throw $texp |] ]
    else do
      let texp = runReader (let ?vars = localVars in tStmExp pexp) formalParams
      pure $ [HS.Qualifier $ maybeWrapThis [hs| throw =<< $texp |] ]

tStm (ABS.AnnStm _ (ABS.STryCatchFinally try_stm cbranches mfinally)) = todo undefined


-- (EFFECTFUL) EXPRESSIONS in statement world
---------------------------------------------

-- | lifting pure expressions into statement world

tEffExp :: ( ?st::SymbolTable, ?fields :: M.Map ABS.LIdent ABS.Type, ?cname :: String) => 
          ABS.EffExp -> Bool -> StmScope HS.Exp
tEffExp (ABS.New qcname args) _ = do
      (locals,fields) <- unzip <$> mapM depends args
      scopeLevels <- get
      let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
          maybeWrapThis = if null fields then id else (\ e -> [hs| (\ this' -> $e) =<< readIORef this|])
          (q, cname) = splitQType qcname
          smartCon = HS.Var $ (if null q then HS.UnQual else HS.Qual $ HS.ModuleName q) $ HS.Ident $ "smart'" ++ cname
          initFun = HS.Var $ (if null q then HS.UnQual else HS.Qual $ HS.ModuleName q) $ HS.Ident $ "init'" ++ cname
      if null locals
        then let initApplied = runReader (let ?tyvars = [] in foldlM
                                                        (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                        initFun
                                                        args) formalParams
             in pure $ maybeWrapThis [hs| I'.liftIO (new $smartCon $initApplied) |]
        else do
          let initApplied = runReader (let ?vars = localVars in foldlM
                                                   (\ acc nextArg -> HS.App acc <$> tStmExp nextArg)
                                                   initFun
                                                   args) formalParams
          pure $ maybeWrapThis [hs| (I'.liftIO . new $smartCon) =<< $initApplied |]
tEffExp (ABS.NewLocal qcname args) _ = do
      (locals,fields) <- unzip <$> mapM depends args
      scopeLevels <- get
      let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
          maybeWrapThis = if null fields then id else (\ e -> [hs| (\ this' -> $e) =<< readIORef this|])
          (q, cname) = splitQType qcname
          smartCon = HS.Var $ (if null q then HS.UnQual else HS.Qual $ HS.ModuleName q) $ HS.Ident $ "smart'" ++ cname
          initFun = HS.Var $ (if null q then HS.UnQual else HS.Qual $ HS.ModuleName q) $ HS.Ident $ "init'" ++ cname
      if null locals
         then let initApplied = runReader (let ?tyvars = [] in foldlM
                                                         (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                         initFun
                                                         args) formalParams
              in pure $ maybeWrapThis [hs| newlocal' $smartCon $initApplied this |]
         else do
           let initApplied = runReader (let ?vars = localVars in foldlM
                                                    (\ acc nextArg -> HS.App acc <$> tStmExp nextArg)
                                                    initFun
                                                    args) formalParams
           pure $ maybeWrapThis [hs| (newlocal' this $smartCon) =<< $initApplied |]

-- pexp: PVar, this, null can be compiled, other limitation
tEffExp (ABS.SyncMethCall pexp (ABS.LIdent (p,mname)) args) _ = case pexp of
  ABS.EVar ident -> do
    typ <- M.lookup ident . M.unions <$> get -- check type in the scopes
    case typ of
      Just (ABS.TSimple qtyp) -> do -- only interface type
          (locals,fields) <- unzip <$> mapM depends args
          scopeLevels <- get
          let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
              maybeWrapThis = if null fields then id else (\ e -> [hs| (\ this' -> $e) =<< readIORef this|])
              (prefix, iident) = splitQType qtyp
              iname = (if null prefix then HS.UnQual else HS.Qual $ HS.ModuleName prefix) $ HS.Ident iident
          if null locals
            then let mapplied = runReader (let ?tyvars = [] in foldlM
                                                         (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                         (HS.Var $ HS.UnQual $ HS.Ident mname)
                                                         args) formalParams
                 in pure $ maybeWrapThis $ HS.Lambda noLoc [HS.PApp iname [HS.PVar $ HS.Ident "obj''"]] [hs| obj'' <.> $mapplied |]
            else do
              let mapplied = runReader (let ?vars = localVars in foldlM
                                                    (\ acc nextArg -> HS.App acc <$> tStmExp nextArg)
                                                    (HS.Var $ HS.UnQual $ HS.Ident mname)
                                                    args) formalParams
              pure $ maybeWrapThis $ HS.Lambda noLoc [HS.PApp iname [HS.PVar $ HS.Ident "obj''"]] [hs| (obj'' <.>) =<< $mapplied |]
      Nothing -> errorPos p "cannot find variable"
      _ -> errorPos p "invalid object callee type"
  ABS.ELit ABS.LNull -> errorPos p "null cannot be the object callee"
  _ -> errorPos p "current compiler limitation: the object callee cannot be an arbitrary pure-exp"

tEffExp (ABS.ThisSyncMethCall (ABS.LIdent (_,mname)) args) _ = do
  (locals,fields) <- unzip <$> mapM depends args
  scopeLevels <- get
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
      maybeWrapThis = if null fields then id else (\ e -> [hs| (\ this' -> $e) =<< readIORef this|])
  if null locals
    then let mapplied = runReader (let ?tyvars = [] in foldlM
                                               (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                               (HS.Var $ HS.UnQual $ HS.Ident mname)
                                               args) formalParams
         in pure $ maybeWrapThis [hs| this <..> $mapplied |]
    else do
      let mapplied = runReader (let ?vars = localVars in foldlM
                                              (\ acc nextArg -> HS.App acc <$> tStmExp nextArg)
                                              (HS.Var $ HS.UnQual $ HS.Ident mname)
                                              args) formalParams
      pure $ maybeWrapThis [hs| (this <..>) =<< $mapplied |]

-- pexp: PVar, this, null can be compiled, other limitation
tEffExp (ABS.AsyncMethCall pexp (ABS.LIdent (p,mname)) args) isAlone = case pexp of
  ABS.EVar ident -> do
    typ <- M.lookup ident . M.unions <$> get -- check type in the scopes
    case typ of
      Just (ABS.TSimple qtyp) -> do -- only interface type
          (locals,fields) <- unzip <$> mapM depends args
          scopeLevels <- get
          let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
              maybeWrapThis = if null fields then id else (\ e -> [hs| (\ this' -> $e) =<< readIORef this|])
              (prefix, iident) = splitQType qtyp
              iname = (if null prefix then HS.UnQual else HS.Qual $ HS.ModuleName prefix) $ HS.Ident iident
          if null locals
            then let mapplied = runReader (let ?tyvars = [] in foldlM
                                                         (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                         (HS.Var $ HS.UnQual $ HS.Ident mname) args) formalParams
                 in pure $ maybeWrapThis $ HS.Lambda noLoc [HS.PApp iname [HS.PVar $ HS.Ident "obj''"]] $ if isAlone
                                                                                                          then [hs| I'.liftIO (obj'' <!!> $mapplied) |] -- optimized, fire&forget
                                                                                                          else [hs| I'.liftIO (obj'' <!> $mapplied) |]
            else do
              let mapplied = runReader (let ?vars = localVars in  foldlM (\ acc nextArg -> HS.App acc <$> tStmExp nextArg)
                                                    (HS.Var $ HS.UnQual $ HS.Ident mname)
                                                    args) formalParams
              pure $ maybeWrapThis $ HS.Lambda noLoc [HS.PApp iname [HS.PVar $ HS.Ident "obj''"]] $ if isAlone
                                                                                                    then [hs| (I'.liftIO . obj'' <!!>) =<< $mapplied |] -- optimized, fire&forget
                                                                                                    else [hs| (I'.liftIO . obj'' <!>) =<< $mapplied |]
      Nothing -> errorPos p "cannot find variable"
      _ -> errorPos p "invalid object callee type"
  ABS.ELit ABS.LNull -> errorPos p "null cannot be the object callee"
  _ -> errorPos p "current compiler limitation: the object callee cannot be an arbitrary pure-exp"
  
tEffExp (ABS.ThisAsyncMethCall (ABS.LIdent (_,mname)) args) isAlone = do
  (locals,fields) <- unzip <$> mapM depends args
  scopeLevels <- get
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
      maybeWrapThis = if null fields then id else (\ e -> [hs| (\ this' -> $e) =<< readIORef this|])
  if null locals
    then let mapplied = runReader (let ?tyvars = [] in foldlM
                                               (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                               (HS.Var $ HS.UnQual $ HS.Ident mname)
                                               args) formalParams
         in pure (maybeWrapThis $ if isAlone 
                                  then [hs| I'.liftIO (this <!!> $mapplied) |] -- optimized, fire&forget
                                  else [hs| I'.liftIO (this <!> $mapplied) |])
    else do
      let mapplied = runReader (let ?vars = localVars in foldlM
                                            (\ acc nextArg -> HS.App acc <$> tStmExp nextArg)
                                            (HS.Var $ HS.UnQual $ HS.Ident mname)
                                            args) formalParams
      pure $ maybeWrapThis $ if isAlone 
                             then [hs| (I'.liftIO . this <!!>) =<< $mapplied |] -- optimized, fire&forget
                             else [hs| (I'.liftIO . this <!>) =<< $mapplied |]

tEffExp (ABS.Get pexp) _ = do
  (locals,fields) <- depends pexp
  scopeLevels <- get
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
      maybeWrapThis = if null fields then id else (\ e -> [hs| (\ this' -> $e) =<< readIORef this|])
  if null locals
    then let texp = runReader (let ?tyvars = [] in tPureExp pexp) formalParams
         in pure $ maybeWrapThis [hs| I'.liftIO (get $texp) |]
    else do
      let texp = runReader (let ?vars = localVars in tStmExp pexp) formalParams
      pure $ maybeWrapThis [hs| (I'.liftIO . get) =<< $texp |]

-- HELPERS
----------

addToScope :: ABS.Type -> ABS.LIdent -> StmScope ()
addToScope typ var@(ABS.LIdent (p,pid)) = do
  (topscope:restscopes) <- get
  if (any (\ scope -> var `M.member` scope) restscopes)
    then errorPos p $ pid ++ " already defined in an outer scope"
    else put $ M.insertWith (const $ const $ errorPos p $ pid ++ " already defined in this scope") var typ topscope  : restscopes


depends pexp = runReader (depends' pexp ([],[])) . M.unions . init <$> get
    where
 collectPatVars :: ABS.Pattern -> [ABS.LIdent]
 collectPatVars (ABS.PIdent ident) = [ident]
 collectPatVars (ABS.PParamConstr _ pats) = concatMap collectPatVars pats
 collectPatVars _ = []

 depends' pexp (rlocal,rfields) = do
  scope <- ask
  case pexp of
    ABS.EThis ident -> pure (rlocal, ident:rfields)
    ABS.EVar ident -> pure $ if ident `M.member` scope 
                            then (ident:rlocal,rfields)
                            else if ident `M.member` ?fields
                                 then (rlocal,ident:rfields)
                                 else (rlocal, rfields)
    ABS.Let (ABS.Par _ ident) pexpEq pexpIn -> do
                                    (rlocalEq, rfieldsEq) <- depends' pexpEq (rlocal,rfields)
                                    (rlocalIn, rfieldsIn) <- let fields' = ?fields
                                                            in
                                                              let ?fields = M.delete ident fields' 
                                                              in local (M.delete ident) (depends' pexpIn (rlocal, rfields))
                                    pure (rlocalEq++rlocalIn, rfieldsEq++rfieldsIn)
    ABS.Case pexpOf branches -> do
        (rlocalOf, rfieldsOf) <- depends' pexpOf (rlocal,rfields)      
        mapM (\ (ABS.CaseBranc pat pexpBranch) ->
                  let fields' = ?fields
                      idents = collectPatVars pat
                  in
                    let ?fields = foldl (flip M.delete) fields' idents
                    in local (\ scope -> foldl (flip M.delete) scope idents) (depends' pexpBranch (rlocal, rfields))
                  ) branches
        pure (rlocalOf, rfieldsOf)
    ABS.EOr e e' -> foldl (\ (acc1,acc2) (x1,x2) -> (acc1++x1,acc2++x2)) ([],[]) <$> mapM (\ ex -> depends' ex (rlocal, rfields)) [e,e']
    ABS.EAnd e e' -> foldl (\ (acc1,acc2) (x1,x2) -> (acc1++x1,acc2++x2)) ([],[]) <$> mapM (\ ex -> depends' ex (rlocal, rfields)) [e,e']
    ABS.EEq e e' -> foldl (\ (acc1,acc2) (x1,x2) -> (acc1++x1,acc2++x2)) ([],[]) <$> mapM (\ ex -> depends' ex (rlocal, rfields)) [e,e']
    ABS.ENeq e e' -> foldl (\ (acc1,acc2) (x1,x2) -> (acc1++x1,acc2++x2)) ([],[]) <$> mapM (\ ex -> depends' ex (rlocal, rfields)) [e,e']
    ABS.ELt e e' -> foldl (\ (acc1,acc2) (x1,x2) -> (acc1++x1,acc2++x2)) ([],[]) <$> mapM (\ ex -> depends' ex (rlocal, rfields)) [e,e']
    ABS.ELe e e' -> foldl (\ (acc1,acc2) (x1,x2) -> (acc1++x1,acc2++x2)) ([],[]) <$> mapM (\ ex -> depends' ex (rlocal, rfields)) [e,e']
    ABS.EGt e e' -> foldl (\ (acc1,acc2) (x1,x2) -> (acc1++x1,acc2++x2)) ([],[]) <$> mapM (\ ex -> depends' ex (rlocal, rfields)) [e,e']
    ABS.EGe e e' -> foldl (\ (acc1,acc2) (x1,x2) -> (acc1++x1,acc2++x2)) ([],[]) <$> mapM (\ ex -> depends' ex (rlocal, rfields)) [e,e']
    ABS.EAdd e e' -> foldl (\ (acc1,acc2) (x1,x2) -> (acc1++x1,acc2++x2)) ([],[]) <$> mapM (\ ex -> depends' ex (rlocal, rfields)) [e,e']
    ABS.ESub e e' -> foldl (\ (acc1,acc2) (x1,x2) -> (acc1++x1,acc2++x2)) ([],[]) <$> mapM (\ ex -> depends' ex (rlocal, rfields)) [e,e']
    ABS.EMul e e' -> foldl (\ (acc1,acc2) (x1,x2) -> (acc1++x1,acc2++x2)) ([],[]) <$> mapM (\ ex -> depends' ex (rlocal, rfields)) [e,e']
    ABS.EDiv e e' -> foldl (\ (acc1,acc2) (x1,x2) -> (acc1++x1,acc2++x2)) ([],[]) <$> mapM (\ ex -> depends' ex (rlocal, rfields)) [e,e']
    ABS.EMod e e' -> foldl (\ (acc1,acc2) (x1,x2) -> (acc1++x1,acc2++x2)) ([],[]) <$> mapM (\ ex -> depends' ex (rlocal, rfields)) [e,e']
    ABS.ELogNeg e -> depends' e (rlocal, rfields)
    ABS.EIntNeg e -> depends' e (rlocal, rfields)
    ABS.EFunCall _ es -> foldl (\ (acc1,acc2) (x1,x2) -> (acc1++x1,acc2++x2)) ([],[]) <$> mapM (\ ex -> depends' ex (rlocal, rfields)) es
    ABS.EQualFunCall _ _ es -> foldl (\ (acc1,acc2) (x1,x2) -> (acc1++x1,acc2++x2)) ([],[]) <$> mapM (\ ex -> depends' ex (rlocal, rfields)) es
    ABS.ENaryFunCall _ es -> foldl (\ (acc1,acc2) (x1,x2) -> (acc1++x1,acc2++x2)) ([],[]) <$> mapM (\ ex -> depends' ex (rlocal, rfields)) es
    ABS.ENaryQualFunCall _ _ es -> foldl (\ (acc1,acc2) (x1,x2) -> (acc1++x1,acc2++x2)) ([],[]) <$> mapM (\ ex -> depends' ex (rlocal, rfields)) es
    ABS.EParamConstr _ es -> foldl (\ (acc1,acc2) (x1,x2) -> (acc1++x1,acc2++x2)) ([],[]) <$> mapM (\ ex -> depends' ex (rlocal, rfields)) es
    ABS.If e e' e'' -> foldl (\ (acc1,acc2) (x1,x2) -> (acc1++x1,acc2++x2)) ([],[]) <$> mapM (\ ex -> depends' ex (rlocal, rfields)) [e,e',e'']
    _ -> return (rlocal, rfields)


