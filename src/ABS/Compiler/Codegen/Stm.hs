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


---------------- LOCAL VARIABLE ASSIGNMENT

tAss _ _ (ABS.LIdent (_,n)) (ABS.ExpP pexp) = do
  scopeLevels <- get
  (locals, fields) <- depends pexp
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
      --maybeWrapThis = if null fields then id else (\ e -> [hs| ((\ this' -> $e) =<< I'.readIORef this) |])
  pure [HS.Qualifier $
         if null locals
         then let texp = runReader (let ?tyvars = [] in tPureExp pexp) formalParams
                  ioAction = [hs| (I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n) $texp) |]
              in [hs| I'.liftIO $ioAction |]
         else let texp = runReader (let ?vars = localVars in tStmExp pexp) formalParams
              in [hs| I'.liftIO (I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n) =<< $texp) |] ]


tAss _ t (ABS.LIdent (_,n)) (ABS.ExpE (ABS.New qcname args)) = do
  scopeLevels <- get
  (locals,fields) <- unzip <$> mapM depends args
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
      --maybeWrapThis = if null (concat fields) then id else (\ e -> [hs| (\ this' -> $e) =<< I'.readIORef this|])
      (q, cname) = splitQType qcname
      smartCon = HS.Var $ (if null q then HS.UnQual else HS.Qual $ HS.ModuleName q) $ HS.Ident $ "smart'" ++ cname
      initFun = HS.Var $ (if null q then HS.UnQual else HS.Qual $ HS.ModuleName q) $ HS.Ident $ "init'" ++ cname
      ABS.TSimple qtyp = t
  pure [HS.Qualifier $ 
         if null (concat locals)
         then let smartApplied = runReader (let ?tyvars = [] in foldlM
                                                         (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                         smartCon
                                                         args) formalParams
                  ioAction = [hs| ((I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n) . $(HS.Var $ HS.UnQual $ HS.Ident $ showQType qtyp)) =<< new $initFun $smartApplied) |]
              in [hs| I'.liftIO $ioAction |]
         else let smartApplied = runReader (let ?vars = localVars in foldlM
                                               (\ acc nextArg -> HS.App acc <$> tStmExp nextArg)
                                               smartCon
                                               args) formalParams
              in [hs| I'.liftIO ((I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n) . $(HS.Var $ HS.UnQual $ HS.Ident $ showQType qtyp)) =<< (new $initFun =<< $smartApplied)) |] ]

tAss _ t (ABS.LIdent (_,n)) (ABS.ExpE (ABS.NewLocal qcname args)) = do
  scopeLevels <- get
  (locals,fields) <- unzip <$> mapM depends args
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
      --maybeWrapThis = if null (concat fields) then id else (\ e -> [hs| (\ this' -> $e) =<< I'.readIORef this|])
      (q, cname) = splitQType qcname
      smartCon = HS.Var $ (if null q then HS.UnQual else HS.Qual $ HS.ModuleName q) $ HS.Ident $ "smart'" ++ cname
      initFun = HS.Var $ (if null q then HS.UnQual else HS.Qual $ HS.ModuleName q) $ HS.Ident $ "init'" ++ cname
      ABS.TSimple qtyp = t
  pure [HS.Qualifier $
         if null (concat locals)
         then let smartApplied = runReader (let ?tyvars = [] in foldlM
                                                         (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                         smartCon
                                                         args) formalParams
                  ioAction = [hs| ((I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n) . $(HS.Var $ HS.UnQual $ HS.Ident $ showQType qtyp)) =<< newlocal' this $initFun $smartApplied) |]
              in [hs| I'.liftIO $ioAction |]
         else let smartApplied = runReader (let ?vars = localVars in foldlM
                                               (\ acc nextArg -> HS.App acc <$> tStmExp nextArg)
                                               smartCon
                                               args) formalParams
              in [hs| I'.liftIO ((I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n) . $(HS.Var $ HS.UnQual $ HS.Ident $ showQType qtyp)) =<< (newlocal' this $initFun =<< $smartApplied)) |] ]

tAss _ _ (ABS.LIdent (_,n)) (ABS.ExpE (ABS.SyncMethCall pexp (ABS.LIdent (p,mname)) args)) = do
  case pexp of
   ABS.EVar ident@(ABS.LIdent (_,calleeVar)) -> do
    typ <- M.lookup ident . M.unions <$> get -- check type in the scopes
    case typ of
      Just (ABS.TSimple qtyp) -> do -- only interface type
          scopeLevels <- get
          (locals,fields) <- unzip <$> mapM depends args
          let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
              --maybeWrapThis = if null (concat fields) then id else (\ e -> [hs| (\ this' -> $e) =<< I'.readIORef this|])
              (prefix, iident) = splitQType qtyp
              iname = (if null prefix then HS.UnQual else HS.Qual $ HS.ModuleName prefix) $ HS.Ident iident
          pure [ HS.Qualifier $
                 if null (concat locals)
                 then let mapplied = runReader (let ?tyvars = [] in foldlM
                                                              (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                              (HS.Var $ HS.UnQual $ HS.Ident mname)
                                                              args) formalParams
                          mwrapped = HS.Lambda noLoc [HS.PApp iname [HS.PVar $ HS.Ident "obj''"]] [hs| sync' this obj'' $mapplied |]
                      in [hs| (I'.liftIO . I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n)) =<< (($mwrapped) =<< I'.liftIO (I'.readIORef $(HS.Var $ HS.UnQual $ HS.Ident calleeVar))) |]
                 else let mapplied = runReader (let ?vars = localVars in foldlM
                                                         (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs| $acc <*> $targ |])
                                                         [hs| I'.pure $(HS.Var $ HS.UnQual $ HS.Ident mname) |]
                                                         args) formalParams
                          mwrapped = HS.Lambda noLoc [HS.PApp iname [HS.PVar $ HS.Ident "obj''"]] [hs| sync' this obj'' =<< I'.liftIO ($mapplied) |]
                      in [hs| (I'.liftIO . I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n)) =<< (($mwrapped) =<< I'.liftIO (I'.readIORef $(HS.Var $ HS.UnQual $ HS.Ident calleeVar))) |]
               ]
      Nothing -> errorPos p "cannot find variable"
      _ -> errorPos p "invalid object callee type"
   ABS.ELit ABS.LNull -> errorPos p "null cannot be the object callee"
   _ -> errorPos p "current compiler limitation: the object callee cannot be an arbitrary pure-exp"

tAss _ _ (ABS.LIdent (_,n)) (ABS.ExpE (ABS.ThisSyncMethCall (ABS.LIdent (_,mname)) args)) = do
  scopeLevels <- get
  (locals,fields) <- unzip <$> mapM depends args
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
      --maybeWrapThis = if null (concat fields) then id else (\ e -> [hs| (\ this' -> $e) =<< I'.readIORef this|])
  pure [HS.Qualifier $
         if null (concat locals)
         then let mapplied = runReader (let ?tyvars = [] in foldlM
                                                      (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                      (HS.Var $ HS.UnQual $ HS.Ident mname)
                                                      args) formalParams
              in [hs| (I'.liftIO . I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n)) =<< (this <..> $mapplied) |]
         else let mapplied = runReader (let ?vars = localVars in foldlM
                                                 (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs| $acc <*> $targ |])
                                                 [hs| I'.pure $(HS.Var $ HS.UnQual $ HS.Ident mname) |]
                                                 args) formalParams
              in [hs| (I'.liftIO . I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n)) =<< ((this <..>) =<< I'.liftIO ($mapplied)) |] ]

tAss _ _ (ABS.LIdent (_,n)) (ABS.ExpE (ABS.AsyncMethCall pexp (ABS.LIdent (p,mname)) args)) = do
 case pexp of
  ABS.EVar ident@(ABS.LIdent (_, calleeVar)) -> do
    typ <- M.lookup ident . M.unions <$> get -- check type in the scopes
    case typ of
      Just (ABS.TSimple qtyp) -> do -- only interface type
          scopeLevels <- get
          (locals,fields) <- unzip <$> mapM depends args
          let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
              --maybeWrapThis = if null (concat fields) then id else (\ e -> [hs| (\ this' -> $e) =<< I'.readIORef this|])
              (prefix, iident) = splitQType qtyp
              iname = (if null prefix then HS.UnQual else HS.Qual $ HS.ModuleName prefix) $ HS.Ident iident
          pure [HS.Qualifier $
                 if null (concat locals)
                 then let mapplied = runReader (let ?tyvars = [] in foldlM
                                                         (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                         (HS.Var $ HS.UnQual $ HS.Ident mname) args) formalParams
                          mwrapped = HS.Lambda noLoc [HS.PApp iname [HS.PVar $ HS.Ident "obj''"]] [hs| (obj'' <!> $mapplied) |]
                          ioAction = [hs| I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n) =<< (($mwrapped) =<< I'.readIORef $(HS.Var $ HS.UnQual $ HS.Ident calleeVar)) |]
                      in [hs| I'.liftIO ($ioAction) |]
                 else let mapplied = runReader (let ?vars = localVars in foldlM
                                                                            (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs| $acc <*> $targ |])
                                                                            [hs| I'.pure $(HS.Var $ HS.UnQual $ HS.Ident mname) |]
                                                                            args) formalParams
                          mwrapped = HS.Lambda noLoc [HS.PApp iname [HS.PVar $ HS.Ident "obj''"]] [hs| (obj'' <!>) =<< $mapplied |]
                      in [hs| I'.liftIO (I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n) =<< (($mwrapped) =<< I'.readIORef $(HS.Var $ HS.UnQual $ HS.Ident calleeVar))) |] ]
      Nothing -> errorPos p "cannot find variable"
      _ -> errorPos p "invalid object callee type"
  ABS.ELit ABS.LNull -> errorPos p "null cannot be the object callee"
  _ -> errorPos p "current compiler limitation: the object callee cannot be an arbitrary pure-exp"

tAss _ _ (ABS.LIdent (_,n)) (ABS.ExpE (ABS.ThisAsyncMethCall (ABS.LIdent (_,mname)) args)) = do
  scopeLevels <- get
  (locals,fields) <- unzip <$> mapM depends args
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
      --maybeWrapThis = if null (concat fields) then id else (\ e -> [hs| (\ this' -> $e) =<< I'.readIORef this|])
  pure [HS.Qualifier $
         if null (concat locals)
         then let mapplied = runReader (let ?tyvars = [] in foldlM
                                               (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                               (HS.Var $ HS.UnQual $ HS.Ident mname)
                                               args) formalParams
                  ioAction = [hs| (I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n) =<< (this <!> $mapplied)) |]
              in [hs| I'.liftIO $ioAction  |]
         else let mapplied = runReader (let ?vars = localVars in foldlM
                                                                      (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs| $acc <*> $targ |])
                                                                      [hs| I'.pure $(HS.Var $ HS.UnQual $ HS.Ident mname) |]
                                                                      args) formalParams
              in [hs| I'.liftIO (I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n) =<< ((this <!>) =<< $mapplied)) |] ]

tAss _ _ (ABS.LIdent (_,n)) (ABS.ExpE (ABS.Get pexp)) = do
  scopeLevels <- get
  (locals,fields) <- depends pexp
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
      --maybeWrapThis = if null fields then id else (\ e -> [hs| (\ this' -> $e) =<< I'.readIORef this|])
  pure [HS.Qualifier $
         if null locals
         then let texp = runReader (let ?tyvars = [] in tPureExp pexp) formalParams
                  ioAction = [hs| (I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n) =<< (get $texp)) |]
              in [hs| I'.liftIO $ioAction |]
         else let texp = runReader (let ?vars = localVars in tStmExp pexp) formalParams
              in [hs| I'.liftIO (I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n) =<< (get =<< $texp)) |] ]


------------- DECLARATION+LOCAL VARIABLE ASSIGNMENT

tStm (ABS.AnnStm _ (ABS.SDecAss t i@(ABS.LIdent (_,n)) (ABS.ExpP pexp))) = do
  scopeLevels <- addToScope t i
  (locals, fields) <- depends pexp
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
      --maybeWrapThis = if null fields then id else (\ e -> [hs| (\ this' -> $e) =<< I'.readIORef this|])
  pure [HS.Generator noLoc 
        (HS.PatTypeSig noLoc (HS.PVar $ HS.Ident n) (HS.TyApp (HS.TyCon $ HS.UnQual $ HS.Ident "IORef'") (tType t))) $
         if null locals
         then let texp = runReader (let ?tyvars = [] in tPureExp pexp) formalParams
                  ioAction = [hs| (I'.newIORef $texp) |]
              in [hs| I'.liftIO $ioAction  |]
         else let texp = runReader (let ?vars = localVars in tStmExp pexp) formalParams
              in [hs| I'.liftIO (I'.newIORef =<< $texp) |] ]


tStm (ABS.AnnStm _ (ABS.SDecAss t i@(ABS.LIdent (_,n)) (ABS.ExpE (ABS.New qcname args)))) = do
  scopeLevels <- addToScope t i
  (locals,fields) <- unzip <$> mapM depends args
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
      --maybeWrapThis = if null (concat fields) then id else (\ e -> [hs| (\ this' -> $e) =<< I'.readIORef this|])
      (q, cname) = splitQType qcname
      smartCon = HS.Var $ (if null q then HS.UnQual else HS.Qual $ HS.ModuleName q) $ HS.Ident $ "smart'" ++ cname
      initFun = HS.Var $ (if null q then HS.UnQual else HS.Qual $ HS.ModuleName q) $ HS.Ident $ "init'" ++ cname
      ABS.TSimple qtyp = t
  pure [HS.Generator noLoc 
        (HS.PatTypeSig noLoc (HS.PVar $ HS.Ident n) (HS.TyApp (HS.TyCon $ HS.UnQual $ HS.Ident "IORef'") (tType t))) $ -- typed
         if null (concat locals)
         then let smartApplied = runReader (let ?tyvars = [] in foldlM
                                           (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                           smartCon
                                           args) formalParams
                  ioAction = [hs| ((I'.newIORef . $(HS.Var $ HS.UnQual $ HS.Ident $ showQType qtyp)) =<< new $initFun $smartApplied) |]
              in [hs| I'.liftIO $ioAction  |]
         else let smartApplied = runReader (let ?vars = localVars in foldlM
                                               (\ acc nextArg -> HS.App acc <$> tStmExp nextArg)
                                               smartCon
                                               args) formalParams
              in [hs| I'.liftIO ((I'.newIORef . $(HS.Var $ HS.UnQual $ HS.Ident $ showQType qtyp)) =<< (new $initFun =<< $smartApplied)) |] ]

tStm (ABS.AnnStm _ (ABS.SDecAss t i@(ABS.LIdent (_,n)) (ABS.ExpE (ABS.NewLocal qcname args)))) = do
  scopeLevels <- addToScope t i
  (locals,fields) <- unzip <$> mapM depends args
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
      --maybeWrapThis = if null (concat fields) then id else (\ e -> [hs| (\ this' -> $e) =<< I'.readIORef this|])
      (q, cname) = splitQType qcname
      smartCon = HS.Var $ (if null q then HS.UnQual else HS.Qual $ HS.ModuleName q) $ HS.Ident $ "smart'" ++ cname
      initFun = HS.Var $ (if null q then HS.UnQual else HS.Qual $ HS.ModuleName q) $ HS.Ident $ "init'" ++ cname
      ABS.TSimple qtyp = t
  pure [HS.Generator noLoc 
        (HS.PatTypeSig noLoc (HS.PVar $ HS.Ident n) (HS.TyApp (HS.TyCon $ HS.UnQual $ HS.Ident "IORef'") (tType t))) $ -- typed
         if null (concat locals)
         then let smartApplied = runReader (let ?tyvars = [] in foldlM
                                           (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                           smartCon
                                           args) formalParams
                  ioAction = [hs| ((I'.newIORef . $(HS.Var $ HS.UnQual $ HS.Ident $ showQType qtyp)) =<< newlocal' this $initFun $smartApplied) |]
              in [hs| I'.liftIO $ioAction |]
         else let smartApplied = runReader (let ?vars = localVars in foldlM
                                               (\ acc nextArg -> HS.App acc <$> tStmExp nextArg)
                                               smartCon
                                               args) formalParams
              in [hs| I'.liftIO ((I'.newIORef . $(HS.Var $ HS.UnQual $ HS.Ident $ showQType qtyp)) =<< (newlocal' this $initFun =<< $smartApplied)) |] ]


tStm (ABS.AnnStm _ (ABS.SDecAss t i@(ABS.LIdent (_,n)) (ABS.ExpE (ABS.SyncMethCall pexp (ABS.LIdent (p,mname)) args)))) = do
  case pexp of
   ABS.EVar ident@(ABS.LIdent (_, calleeVar)) -> do
    typ <- M.lookup ident . M.unions <$> get -- check type in the scopes
    case typ of
      Just (ABS.TSimple qtyp) -> do -- only interface type
          scopeLevels <- addToScope t i
          (locals,fields) <- unzip <$> mapM depends args
          let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
              --maybeWrapThis = if null (concat fields) then id else (\ e -> [hs| (\ this' -> $e) =<< I'.readIORef this|])
              (prefix, iident) = splitQType qtyp
              iname = (if null prefix then HS.UnQual else HS.Qual $ HS.ModuleName prefix) $ HS.Ident iident
          pure [HS.Generator noLoc 
                (HS.PatTypeSig noLoc (HS.PVar $ HS.Ident n) (HS.TyApp (HS.TyCon $ HS.UnQual $ HS.Ident "IORef'") (tType t))) $
                 if null (concat locals)
                 then let mapplied = runReader (let ?tyvars = [] in foldlM
                                                              (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                              (HS.Var $ HS.UnQual $ HS.Ident mname)
                                                              args) formalParams
                          mwrapped = HS.Lambda noLoc [HS.PApp iname [HS.PVar $ HS.Ident "obj''"]] [hs| sync' this obj'' $mapplied |]
                      in [hs| (I'.liftIO . I'.newIORef) =<< (($mwrapped) =<< I'.liftIO (I'.readIORef $(HS.Var $ HS.UnQual $ HS.Ident calleeVar))) |]
                 else let mapplied = runReader (let ?vars = localVars in foldlM
                                                         (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs| $acc <*> $targ |])
                                                         [hs| I'.pure $(HS.Var $ HS.UnQual $ HS.Ident mname) |]
                                                         args) formalParams
                          mwrapped = HS.Lambda noLoc [HS.PApp iname [HS.PVar $ HS.Ident "obj''"]] [hs| sync' this obj'' =<< I'.liftIO ($mapplied) |]
                      in [hs| (I'.liftIO . I'.newIORef) =<< (($mwrapped) =<< I'.liftIO (I'.readIORef $(HS.Var $ HS.UnQual $ HS.Ident calleeVar))) |] ]
      Nothing -> errorPos p "cannot find variable"
      _ -> errorPos p "invalid object callee type"
   ABS.ELit ABS.LNull -> errorPos p "null cannot be the object callee"
   _ -> errorPos p "current compiler limitation: the object callee cannot be an arbitrary pure-exp"

tStm (ABS.AnnStm _ (ABS.SDecAss t i@(ABS.LIdent (_,n)) (ABS.ExpE (ABS.ThisSyncMethCall (ABS.LIdent (_,mname)) args)))) = do
  scopeLevels <- addToScope t i
  (locals,fields) <- unzip <$> mapM depends args
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
      --maybeWrapThis = if null (concat fields) then id else (\ e -> [hs| (\ this' -> $e) =<< I'.readIORef this|])
  pure [HS.Generator noLoc 
        (HS.PatTypeSig noLoc (HS.PVar $ HS.Ident n) (HS.TyApp (HS.TyCon $ HS.UnQual $ HS.Ident "IORef'") (tType t))) $
         if null (concat locals)
         then let mapplied = runReader (let ?tyvars = [] in foldlM
                                                      (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                      (HS.Var $ HS.UnQual $ HS.Ident mname)
                                                      args) formalParams
              in [hs| (I'.liftIO . I'.newIORef) =<< (this <..> $mapplied) |]
         else let mapplied = runReader (let ?vars = localVars in foldlM
                                                 (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs| $acc <*> $targ |])
                                                 [hs| I'.pure $(HS.Var $ HS.UnQual $ HS.Ident mname) |]
                                                 args) formalParams
              in [hs| (I'.liftIO . I'.newIORef) =<< ((this <..>) =<< I'.liftIO ($mapplied)) |] ]

tStm (ABS.AnnStm _ (ABS.SDecAss t i@(ABS.LIdent (_,n)) (ABS.ExpE (ABS.AsyncMethCall pexp (ABS.LIdent (p,mname)) args)))) = do
 case pexp of
  ABS.EVar ident@(ABS.LIdent (_,calleeVar)) -> do
    typ <- M.lookup ident . M.unions <$> get -- check type in the scopes
    case typ of
      Just (ABS.TSimple qtyp) -> do -- only interface type
          scopeLevels <- addToScope t i
          (locals,fields) <- unzip <$> mapM depends args
          let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
              --maybeWrapThis = if null (concat fields) then id else (\ e -> [hs| (\ this' -> $e) =<< I'.readIORef this|])
              (prefix, iident) = splitQType qtyp
              iname = (if null prefix then HS.UnQual else HS.Qual $ HS.ModuleName prefix) $ HS.Ident iident
          pure [HS.Generator noLoc 
                (HS.PatTypeSig noLoc (HS.PVar $ HS.Ident n) (HS.TyApp (HS.TyCon $ HS.UnQual $ HS.Ident "IORef'") (tType t))) $
                 if null (concat locals)
                 then let mapplied = runReader (let ?tyvars = [] in foldlM
                                                         (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                         (HS.Var $ HS.UnQual $ HS.Ident mname) args) formalParams
                          mwrapped = HS.Lambda noLoc [HS.PApp iname [HS.PVar $ HS.Ident "obj''"]] [hs| (obj'' <!> $mapplied) |]
                          ioAction = [hs| I'.newIORef =<< (($mwrapped) =<< I'.readIORef $(HS.Var $ HS.UnQual $ HS.Ident calleeVar)) |]
                      in [hs| I'.liftIO ($ioAction) |]
                 else let mapplied = runReader (let ?vars = localVars in foldlM 
                                                                            (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs| $acc <*> $targ |])
                                                                            [hs| I'.pure $(HS.Var $ HS.UnQual $ HS.Ident mname) |]
                                                                            args) formalParams
                          mwrapped = HS.Lambda noLoc [HS.PApp iname [HS.PVar $ HS.Ident "obj''"]] [hs| (obj'' <!>) =<< $mapplied |]
                      in [hs| I'.liftIO (I'.newIORef =<< (($mwrapped) =<< I'.readIORef $(HS.Var $ HS.UnQual $ HS.Ident calleeVar))) |] ]
      Nothing -> errorPos p "cannot find variable"
      _ -> errorPos p "invalid object callee type"
  ABS.ELit ABS.LNull -> errorPos p "null cannot be the object callee"
  _ -> errorPos p "current compiler limitation: the object callee cannot be an arbitrary pure-exp"

tStm (ABS.AnnStm _ (ABS.SDecAss t i@(ABS.LIdent (_,n)) (ABS.ExpE (ABS.ThisAsyncMethCall (ABS.LIdent (_,mname)) args)))) = do
  scopeLevels <- addToScope t i
  (locals,fields) <- unzip <$> mapM depends args
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
      --maybeWrapThis = if null (concat fields) then id else (\ e -> [hs| (\ this' -> $e) =<< I'.readIORef this|])
  pure [HS.Generator noLoc 
        (HS.PatTypeSig noLoc (HS.PVar $ HS.Ident n) (HS.TyApp (HS.TyCon $ HS.UnQual $ HS.Ident "IORef'") (tType t))) $
         if null (concat locals)
         then let mapplied = runReader (let ?tyvars = [] in foldlM
                                               (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                               (HS.Var $ HS.UnQual $ HS.Ident mname)
                                               args) formalParams
                  ioAction = [hs| (I'.newIORef =<< (this <!> $mapplied)) |]
              in [hs| I'.liftIO $ioAction |]
         else let mapplied = runReader (let ?vars = localVars in foldlM
                                                                      (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs| $acc <*> $targ |])
                                                                      [hs| I'.pure $(HS.Var $ HS.UnQual $ HS.Ident mname) |]
                                                                      args) formalParams
              in [hs| I'.liftIO (I'.newIORef =<< ((this <!>) =<< $mapplied)) |] ]

tStm (ABS.AnnStm _ (ABS.SDecAss t i@(ABS.LIdent (_,n)) (ABS.ExpE (ABS.Get pexp)))) = do
  scopeLevels <- addToScope t i
  (locals,fields) <- depends pexp
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
      --maybeWrapThis = if null fields then id else (\ e -> [hs| (\ this' -> $e) =<< I'.readIORef this|])
  pure [HS.Generator noLoc 
        (HS.PatTypeSig noLoc (HS.PVar $ HS.Ident n) (HS.TyApp (HS.TyCon $ HS.UnQual $ HS.Ident "IORef'") (tType t))) $
         if null locals
         then let texp = runReader (let ?tyvars = [] in tPureExp pexp) formalParams
                  ioAction = [hs| (I'.newIORef =<< get $texp) |]
              in [hs| I'.liftIO $ioAction |]
         else let texp = runReader (let ?vars = localVars in tStmExp pexp) formalParams
              in [hs| I'.liftIO (I'.newIORef =<< (get =<< $texp)) |] ]


--- DISPATCHER: LOCAL-VARIABLE OR FIELD ASSIGMENT

tStm (ABS.AnnStm a (ABS.SAss i e)) = do
  scope <- M.unions <$> get
  case M.lookup i scope of
    Just typ -> tAss a typ i e 
    Nothing -> if i `M.member` ?fields
              then tStm (ABS.AnnStm a (ABS.SFieldAss i e)) -- normalize it to fieldass
              else error "not in scope"

------------------- FIELD ASSIGNMENT


tStm (ABS.AnnStm _ (ABS.SFieldAss i e)) = todo undefined

------------------------- RETURN , STANDALONE EXPRESSION

tStm (ABS.AnnStm _ (ABS.SReturn (ABS.ExpE eexp))) = return . HS.Qualifier <$> tEffExp eexp False -- not standalone, because we have to capture and return its result
tStm (ABS.AnnStm a (ABS.SReturn (ABS.ExpP pexp))) = tStm (ABS.AnnStm a (ABS.SExp (ABS.ExpP pexp))) -- rewrite to standalone

tStm (ABS.AnnStm _ (ABS.SExp (ABS.ExpE eexp))) = return . HS.Qualifier <$> tEffExp eexp True
tStm (ABS.AnnStm _ (ABS.SExp (ABS.ExpP pexp))) = do
  scopeLevels <- get
  (locals, fields) <- depends pexp
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
      --maybeWrapThis = if null fields then id else (\ e -> [hs| (\ this' -> $e) =<< I'.readIORef this|])
  if null locals
    then let texp = runReader (let ?tyvars = [] in tPureExp pexp) formalParams
         in pure $ [HS.Qualifier [hs| I'.pure $texp |] ]
    else let texp = runReader (let ?vars = localVars in tStmExp pexp) formalParams
         in pure $ [HS.Qualifier [hs| $texp |] ]



---- DECLARATION

tStm (ABS.AnnStm _ (ABS.SDec t i@(ABS.LIdent (p,n)))) = case t of
   -- it is an unitialized future (set to newEmptyMVar)
  ABS.TGen (ABS.QTyp [ABS.QTypeSegmen (ABS.UIdent (_,"Fut"))])  _ -> do
      _ <- addToScope t i
      pure [HS.Generator noLoc 
                   (HS.PatTypeSig noLoc (HS.PVar $ HS.Ident n) (HS.TyApp (HS.TyCon $ HS.UnQual $ HS.Ident "IORef'") (tType t)))   -- f :: IORef (Fut a) <- emptyFuture
                   [hs| I'.liftIO (I'.newIORef =<< emptyFuture) |]]
   -- it may be an object (set to null) or foreign (set to undefined)
  ABS.TSimple qtyp -> let
                       (prefix, ident) = splitQType qtyp
                       Just (SV symbolType _) = if null prefix
                                                then M.lookup (SN ident Nothing) ?st
                                                else M.lookup (SN ident (Just (prefix, False))) ?st 
                                                           <|> M.lookup (SN ident (Just (prefix, True))) ?st 
                     in case symbolType of
                          Interface _ _ -> do
                                          _ <- addToScope t i
                                          pure [HS.Generator noLoc 
                                                      (HS.PatTypeSig noLoc (HS.PVar $ HS.Ident n) (HS.TyApp (HS.TyCon $ HS.UnQual $ HS.Ident "IORef'") (tType t))) -- o :: IORef Interf <- null
                                                      [hs| I'.liftIO (I'.newIORef ($(HS.Var $ HS.UnQual $ HS.Ident $ showQType qtyp) null)) |] ]
                          Foreign -> do
                            _ <- addToScope t i
                            pure [HS.Generator noLoc (HS.PVar $ HS.Ident n) [hs| I'.liftIO (I'.newIORef undefined) |] ] -- undefined if foreign
                          _ -> errorPos p "A field must be initialised if it is not of a reference type"




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
      --maybeWrapThis = if null fields then id else (\ e -> [hs| (\ this' -> $e) =<< I'.readIORef this|])
  let texp = runReader (let ?vars = localVars in tStmExp pexp) formalParams  -- only treat it as StmExp
  [HS.Qualifier tbody] <- tStm $ ABS.AnnStm [] (ABS.SBlock [stmBody])
  pure $ [HS.Qualifier [hs| while $texp $tbody |] ]              

tStm (ABS.AnnStm _ (ABS.SIf pexp stmThen)) = do
  scopeLevels <- get
  (locals, fields) <- depends pexp
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
      --maybeWrapThis = if null fields then id else (\ e -> [hs| (\ this' -> $e) =<< I'.readIORef this|])
  if null locals
    then do
      let tpred = runReader (let ?tyvars = [] in tPureExp pexp) formalParams
      [HS.Qualifier tthen] <- tStm $ ABS.AnnStm [] (ABS.SBlock [stmThen])
      pure [HS.Qualifier [hs| when $tpred $tthen |]]
    else do
      let tpred = runReader (let ?vars = localVars in tStmExp pexp) formalParams
      [HS.Qualifier tthen] <- tStm $ ABS.AnnStm [] (ABS.SBlock [stmThen])
      pure [ HS.Generator noLoc (HS.PVar $ HS.Ident "when'") tpred
           , HS.Qualifier [hs| when when' $tthen |]]

tStm (ABS.AnnStm _ (ABS.SIfElse pexp stmThen stmElse)) = do
  scopeLevels <- get
  (locals, fields) <- depends pexp
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
      --maybeWrapThis = if null fields then id else (\ e -> [hs| (\ this' -> $e) =<< I'.readIORef this|])
  if null locals
    then do
      let tpred = runReader (let ?tyvars = [] in tPureExp pexp) formalParams
      [HS.Qualifier tthen] <- tStm $ ABS.AnnStm [] (ABS.SBlock [stmThen])
      [HS.Qualifier telse] <- tStm $ ABS.AnnStm [] (ABS.SBlock [stmElse])
      pure [HS.Qualifier [hs| if $tpred then $tthen else $telse |]]
    else do
      let tpred = runReader (let ?vars = localVars in tStmExp pexp) formalParams
      [HS.Qualifier tthen] <- tStm $ ABS.AnnStm [] (ABS.SBlock [stmThen])
      [HS.Qualifier telse] <- tStm $ ABS.AnnStm [] (ABS.SBlock [stmElse])
      pure [ HS.Generator noLoc (HS.PVar $ HS.Ident "if'") tpred
           , HS.Qualifier [hs| if if' then $tthen else $telse |]]

-- OTHER STATEMENTS
--------------------------------

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
      --maybeWrapThis = if null fields then id else (\ e -> [hs| (\ this' -> $e) =<< I'.readIORef this|])
  if null locals
    then do
      let texp = runReader (let ?tyvars = [] in tPureExp pexp) formalParams
      pure $ [HS.Qualifier [hs| I'.liftIO (I'.putStrLn $texp) |] ]
    else do
      let texp = runReader (let ?vars = localVars in tStmExp pexp) formalParams
      pure $ [HS.Qualifier [hs| I'.liftIO (I'.putStrLn =<< $texp) |] ]

-- EXCEPTION STATEMENTS
-------------------------

tStm (ABS.AnnStm _ (ABS.SAssert pexp)) = do
  (locals, fields) <- depends pexp
  scopeLevels <- get
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
      --maybeWrapThis = if null fields then id else (\ e -> [hs| (\ this' -> $e) =<< I'.readIORef this|])
  if null locals
    then do
      let texp = runReader (let ?tyvars = [] in tPureExp pexp) formalParams
      pure $ [HS.Qualifier [hs| assert $texp |] ]
    else do
      let texp = runReader (let ?vars = localVars in tStmExp pexp) formalParams
      pure $ [HS.Qualifier [hs| assert =<< $texp |] ]

tStm (ABS.AnnStm _ (ABS.SThrow pexp)) = do
  (locals, fields) <- depends pexp
  scopeLevels <- get
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
      --maybeWrapThis = if null fields then id else (\ e -> [hs| (\ this' -> $e) =<< I'.readIORef this|])
  if null locals
    then do
      let texp = runReader (let ?tyvars = [] in tPureExp pexp) formalParams
      pure $ [HS.Qualifier [hs| throw $texp |] ]
    else do
      let texp = runReader (let ?vars = localVars in tStmExp pexp) formalParams
      pure $ [HS.Qualifier [hs| throw =<< $texp |] ]

tStm (ABS.AnnStm _ (ABS.STryCatchFinally try_stm cbranches mfinally)) = todo undefined


-- (EFFECTFUL) EXPRESSIONS in statement world
---------------------------------------------

tEffExp :: ( ?st::SymbolTable, ?fields :: M.Map ABS.LIdent ABS.Type, ?cname :: String) => 
          ABS.EffExp -> Bool -> StmScope HS.Exp
tEffExp (ABS.New qcname args) _ = do
      scopeLevels <- get
      (locals,fields) <- unzip <$> mapM depends args
      let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
          --maybeWrapThis = if null (concat fields) then id else (\ e -> [hs| (\ this' -> $e) =<< I'.readIORef this|])
          (q, cname) = splitQType qcname
          smartCon = HS.Var $ (if null q then HS.UnQual else HS.Qual $ HS.ModuleName q) $ HS.Ident $ "smart'" ++ cname
          initFun = HS.Var $ (if null q then HS.UnQual else HS.Qual $ HS.ModuleName q) $ HS.Ident $ "init'" ++ cname
      if null (concat locals)
        then let smartApplied = runReader (let ?tyvars = [] in foldlM
                                                        (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                        smartCon
                                                        args) formalParams
                 ioAction = [hs| (new $initFun $smartApplied) |]
             in pure [hs| I'.liftIO $ioAction |]
        else let smartApplied = runReader (let ?vars = localVars in foldlM
                                                   (\ acc nextArg -> HS.App acc <$> tStmExp nextArg)
                                                   smartCon
                                                   args) formalParams
             in pure [hs| I'.liftIO (new $initFun =<< $smartApplied) |]

tEffExp (ABS.NewLocal qcname args) _ = do
      scopeLevels <- get
      (locals,fields) <- unzip <$> mapM depends args
      let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
          --maybeWrapThis = if null (concat fields) then id else (\ e -> [hs| (\ this' -> $e) =<< I'.readIORef this|])
          (q, cname) = splitQType qcname
          smartCon = HS.Var $ (if null q then HS.UnQual else HS.Qual $ HS.ModuleName q) $ HS.Ident $ "smart'" ++ cname
          initFun = HS.Var $ (if null q then HS.UnQual else HS.Qual $ HS.ModuleName q) $ HS.Ident $ "init'" ++ cname
      if null (concat locals)
        then let smartApplied = runReader (let ?tyvars = [] in foldlM
                                                        (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                        smartCon
                                                        args) formalParams
                 ioAction = [hs| (newlocal' this $initFun $smartApplied) |]
             in pure [hs| I'.liftIO $ioAction |]
        else let smartApplied = runReader (let ?vars = localVars in foldlM
                                                   (\ acc nextArg -> HS.App acc <$> tStmExp nextArg)
                                                   smartCon
                                                   args) formalParams
             in pure [hs| I'.liftIO (newlocal' this $initFun =<< $smartApplied) |]


tEffExp (ABS.SyncMethCall pexp (ABS.LIdent (p,mname)) args) _ = case pexp of
  ABS.EVar ident@(ABS.LIdent (_,calleeVar)) -> do
    typ <- M.lookup ident . M.unions <$> get -- check type in the scopes
    case typ of
      Just (ABS.TSimple qtyp) -> do -- only interface type
          scopeLevels <- get
          (locals,fields) <- unzip <$> mapM depends args
          let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
              --maybeWrapThis = if null (concat fields) then id else (\ e -> [hs| (\ this' -> $e) =<< I'.readIORef this|])
              (prefix, iident) = splitQType qtyp
              iname = (if null prefix then HS.UnQual else HS.Qual $ HS.ModuleName prefix) $ HS.Ident iident
          if null (concat locals)
            then let mapplied = runReader (let ?tyvars = [] in foldlM
                                                         (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                         (HS.Var $ HS.UnQual $ HS.Ident mname)
                                                         args) formalParams
                     mwrapped = HS.Lambda noLoc [HS.PApp iname [HS.PVar $ HS.Ident "obj''"]] [hs| sync' this obj'' $mapplied |]
                 in pure [hs| ($mwrapped) =<< I'.liftIO (I'.readIORef $(HS.Var $ HS.UnQual $ HS.Ident calleeVar)) |]
            else let mapplied = runReader (let ?vars = localVars in foldlM
                                                    (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs| $acc <*> $targ |])
                                                    [hs| I'.pure $(HS.Var $ HS.UnQual $ HS.Ident mname) |]
                                                    args) formalParams
                     mwrapped = HS.Lambda noLoc [HS.PApp iname [HS.PVar $ HS.Ident "obj''"]] [hs| sync' this obj'' =<< I'.liftIO ($mapplied) |]
                 in pure [hs| ($mwrapped) =<< I'.liftIO (I'.readIORef $(HS.Var $ HS.UnQual $ HS.Ident calleeVar)) |]
      Nothing -> errorPos p "cannot find variable"
      _ -> errorPos p "invalid object callee type"
  ABS.ELit ABS.LNull -> errorPos p "null cannot be the object callee"
  _ -> errorPos p "current compiler limitation: the object callee cannot be an arbitrary pure-exp"

tEffExp (ABS.ThisSyncMethCall (ABS.LIdent (_,mname)) args) _ = do
  scopeLevels <- get
  (locals,fields) <- unzip <$> mapM depends args
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
      --maybeWrapThis = if null (concat fields) then id else (\ e -> [hs| (\ this' -> $e) =<< I'.readIORef this|])
  if null (concat locals)
    then let mapplied = runReader (let ?tyvars = [] in foldlM
                                               (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                               (HS.Var $ HS.UnQual $ HS.Ident mname)
                                               args) formalParams
         in pure [hs| this <..> $mapplied |]
    else let mapplied = runReader (let ?vars = localVars in foldlM
                                              (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs| $acc <*> $targ |])
                                              [hs| I'.pure $(HS.Var $ HS.UnQual $ HS.Ident mname) |]
                                              args) formalParams
         in pure [hs| (this <..>) =<< I'.liftIO ($mapplied) |]

tEffExp (ABS.AsyncMethCall pexp (ABS.LIdent (p,mname)) args) isAlone = case pexp of
  ABS.EVar ident@(ABS.LIdent (_,calleeVar)) -> do
    typ <- M.lookup ident . M.unions <$> get -- check type in the scopes
    case typ of
      Just (ABS.TSimple qtyp) -> do -- only interface type
          scopeLevels <- get
          (locals,fields) <- unzip <$> mapM depends args
          let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
              --maybeWrapThis = if null (concat fields) then id else (\ e -> [hs| (\ this' -> $e) =<< I'.readIORef this|])
              (prefix, iident) = splitQType qtyp
              iname = (if null prefix then HS.UnQual else HS.Qual $ HS.ModuleName prefix) $ HS.Ident iident
          if null (concat locals)
            then let mapplied = runReader (let ?tyvars = [] in foldlM
                                                         (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                         (HS.Var $ HS.UnQual $ HS.Ident mname) args) formalParams
                     mwrapped = HS.Lambda noLoc [HS.PApp iname [HS.PVar $ HS.Ident "obj''"]] $ if isAlone
                                                                                               then [hs| (obj'' <!!> $mapplied) |] -- optimized, fire&forget
                                                                                               else [hs| (obj'' <!> $mapplied) |]
                 in pure [hs| I'.liftIO (($mwrapped) =<< (I'.readIORef $(HS.Var $ HS.UnQual $ HS.Ident calleeVar))) |]
            else let mapplied = runReader (let ?vars = localVars in foldlM
                                                    (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs| $acc <*> $targ |])
                                                    [hs| I'.pure $(HS.Var $ HS.UnQual $ HS.Ident mname) |]                                                    
                                                    args) formalParams
                     mwrapped = HS.Lambda noLoc [HS.PApp iname [HS.PVar $ HS.Ident "obj''"]] $ if isAlone
                                                                                               then [hs| (obj'' <!!>) =<< $mapplied |] -- optimized, fire&forget
                                                                                               else [hs| (obj'' <!>) =<< $mapplied |]
                 in pure [hs| I'.liftIO (($mwrapped) =<< (I'.readIORef $(HS.Var $ HS.UnQual $ HS.Ident calleeVar))) |]

      Nothing -> errorPos p "cannot find variable"
      _ -> errorPos p "invalid object callee type"
  ABS.ELit ABS.LNull -> errorPos p "null cannot be the object callee"
  _ -> errorPos p "current compiler limitation: the object callee cannot be an arbitrary pure-exp"
  
tEffExp (ABS.ThisAsyncMethCall (ABS.LIdent (_,mname)) args) isAlone = do
  scopeLevels <- get
  (locals,fields) <- unzip <$> mapM depends args
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
      --maybeWrapThis = if null (concat fields) then id else (\ e -> [hs| (\ this' -> $e) =<< I'.readIORef this|])
  if null (concat locals)
    then let mapplied = runReader (let ?tyvars = [] in foldlM
                                               (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                               (HS.Var $ HS.UnQual $ HS.Ident mname)
                                               args) formalParams
         in pure (if isAlone 
                                  then [hs| I'.liftIO (this <!!> $mapplied) |] -- optimized, fire&forget
                                  else [hs| I'.liftIO (this <!> $mapplied) |])
    else let mapplied = runReader (let ?vars = localVars in foldlM
                                            (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs| $acc <*> $targ |])
                                            [hs| I'.pure $(HS.Var $ HS.UnQual $ HS.Ident mname) |]
                                            args) formalParams
         in pure $ if isAlone 
                                   then [hs| (I'.liftIO . this <!!>) =<< $mapplied |] -- optimized, fire&forget
                                   else [hs| (I'.liftIO . this <!>) =<< $mapplied |]

tEffExp (ABS.Get pexp) _ = do
  scopeLevels <- get
  (locals,fields) <- depends pexp
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
      --maybeWrapThis = if null fields then id else (\ e -> [hs| (\ this' -> $e) =<< I'.readIORef this|])
  if null locals
    then let texp = runReader (let ?tyvars = [] in tPureExp pexp) formalParams
             ioAction = [hs| (get $texp) |]
         in pure [hs| I'.liftIO $ioAction  |]
    else let texp = runReader (let ?vars = localVars in tStmExp pexp) formalParams
         in pure [hs| (I'.liftIO . get) =<< $texp |]

-- HELPERS
----------

addToScope typ var@(ABS.LIdent (p,pid)) = do
  (topscope:restscopes) <- get
  if (any (\ scope -> var `M.member` scope) restscopes)
    then errorPos p $ pid ++ " already defined in an outer scope"
    else let newScopeLevels = M.insertWith (const $ const $ errorPos p $ pid ++ " already defined in this scope") var typ topscope  : restscopes
         in do
           put newScopeLevels
           return newScopeLevels


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


