{-# LANGUAGE CPP, ImplicitParams, QuasiQuotes, LambdaCase #-}
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

import Control.Monad.Trans.State.Strict (evalState, get, put, modify')
import Control.Monad.Trans.Reader (runReader, ask, local)
import qualified Data.Map as M

import Data.Foldable (foldlM)
import Data.List (nub, find)

import Control.Exception (assert)
#define todo assert False

tMethod :: (?st :: SymbolTable) => [ABS.AnnStm] -> [ABS.FormalPar] -> M.Map ABS.L ABS.T -> String -> [String] -> Bool -> HS.Exp
tMethod bodyStms mparams fields cname cAloneMethods isInit = evalState (let ?fields = fields  -- fixed fields passed as an implicit param
                                                                            ?cname = cname    -- className needed for field pattern-matching
                                                                            ?cAloneMethods = cAloneMethods
                                                                            ?isInit = isInit
                                                                        in do
                                                                            tstms <- concat <$> mapM tStm bodyStms
                                                                            pure $ if null tstms
                                                                                   then [hs| return () |] -- otherwise empty rhs
                                                                                   else HS.Do $ case last tstms of 
                                                                                                  HS.Generator _ _ _ ->  tstms ++ [HS.Qualifier $ [hs| I'.pure () |]]
                                                                                                  _ -> tstms)
                                                            [M.empty, -- new scope
                                                             M.fromList (map (\ (ABS.FormalPar t i) -> (i,t)) mparams)] -- first scope level is the formal params


---------------- LOCAL VARIABLE ASSIGNMENT

tAss _ _ (ABS.L (_,n)) (ABS.ExpP pexp) = do
  scopeLevels <- get
  (locals, fields,hasForeigns) <- depends pexp
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
      maybeWrapThis = if null fields then id else (\ e -> [hs| ((\ this'' -> $e) =<< I'.readIORef this') |])
      maybeLift = if ?isInit then id else (\e -> [hs| I'.lift ($e)|])
  pure [HS.Qualifier $
         if null locals && not hasForeigns
         then let texp = runReader (let ?tyvars = [] in tPureExp pexp) formalParams
              in maybeLift $ maybeWrapThis [hs| I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n) $texp |]
         else let texp = runReader (let ?vars = localVars in tStmExp pexp) formalParams
              in maybeLift [hs| I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n) =<< $(maybeWrapThis texp) |] ]

tAss _ (ABS.TSimple qu) (ABS.L (_,n)) (ABS.ExpE (ABS.New qcname args)) = do
  scopeLevels <- get
  (locals,fields,hasForeigns) <- unzip3 <$> mapM depends args
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
      maybeWrapThis = if null (concat fields) then id else (\ e -> [hs| (\ this'' -> $e) =<< I'.readIORef this'|])
      maybeLift = if ?isInit then id else (\e -> [hs| I'.lift ($e)|])
      (q, cname) = splitQU qcname
      smartCon = HS.Var $ (if null q then HS.UnQual else HS.Qual $ HS.ModuleName q) $ HS.Ident $ "smart'" ++ cname
      initFun = HS.Var $ (if null q then HS.UnQual else HS.Qual $ HS.ModuleName q) $ HS.Ident $ "init'" ++ cname
  pure [HS.Qualifier $ 
         if null (concat locals) && not (or hasForeigns)
         then let smartApplied = runReader (let ?tyvars = [] in foldlM
                                                         (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                         smartCon
                                                         args) formalParams
              in maybeLift $ maybeWrapThis [hs| ((I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n) . $(HS.Var $ HS.UnQual $ HS.Ident $ showQU qu)) =<< new $initFun $smartApplied) |]
         else let smartApplied = runReader (let ?vars = localVars in foldlM
                                               (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs| $acc <*> $targ |])
                                               [hs| I'.pure $smartCon |]
                                               args) formalParams
              in maybeLift [hs| (I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n) . $(HS.Var $ HS.UnQual $ HS.Ident $ showQU qu)) =<< (new $initFun =<< $(maybeWrapThis smartApplied)) |] ]

tAss _ (ABS.TSimple qu) (ABS.L (_,n)) (ABS.ExpE (ABS.NewLocal qcname args)) = do
  scopeLevels <- get
  (locals,fields,hasForeigns) <- unzip3 <$> mapM depends args
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
      maybeWrapThis = if null (concat fields) then id else (\ e -> [hs| (\ this'' -> $e) =<< I'.readIORef this'|])
      maybeLift = if ?isInit then id else (\e -> [hs| I'.lift ($e)|])
      (q, cname) = splitQU qcname
      smartCon = HS.Var $ (if null q then HS.UnQual else HS.Qual $ HS.ModuleName q) $ HS.Ident $ "smart'" ++ cname
      initFun = HS.Var $ (if null q then HS.UnQual else HS.Qual $ HS.ModuleName q) $ HS.Ident $ "init'" ++ cname
  pure [HS.Qualifier $
         if null (concat locals) && not (or hasForeigns)
         then let smartApplied = runReader (let ?tyvars = [] in foldlM
                                                         (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                         smartCon
                                                         args) formalParams
              in maybeLift $ maybeWrapThis [hs| ((I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n) . $(HS.Var $ HS.UnQual $ HS.Ident $ showQU qu)) =<< newlocal' this $initFun $smartApplied) |]
         else let smartApplied = runReader (let ?vars = localVars in foldlM
                                               (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs| $acc <*> $targ |])
                                               [hs| I'.pure $smartCon |]
                                               args) formalParams
              in maybeLift [hs| (I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n) . $(HS.Var $ HS.UnQual $ HS.Ident $ showQU qu)) =<< (newlocal' this $initFun =<< $(maybeWrapThis smartApplied)) |] ]

tAss a typ i@(ABS.L (_,n)) (ABS.ExpE (ABS.SyncMethCall pexp (ABS.L (p,mname)) args)) =
  case pexp of
   ABS.EVar ident@(ABS.L (_,calleeVar)) -> do
    scopeLevels <- get
    case M.lookup ident (M.unions scopeLevels) of      -- check type in the scopes
      Just (ABS.TSimple qu) -> do -- only interface type
          (locals,fields,hasForeigns) <- unzip3 <$> mapM depends args
          let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
              maybeWrapThis = if null (concat fields) then id else (\ e -> [hs| (\ this'' -> $e) =<< I'.lift (I'.readIORef this')|])
              (prefix, iident) = splitQU qu
              iname = (if null prefix then HS.UnQual else HS.Qual $ HS.ModuleName prefix) $ HS.Ident iident
          pure [ HS.Qualifier $
                 if null (concat locals) && not (or hasForeigns)
                 then let mapplied = runReader (let ?tyvars = [] in foldlM
                                                              (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                              (HS.Var $ HS.UnQual $ HS.Ident mname)
                                                              args) formalParams
                          mwrapped = HS.Lambda noLoc [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs| sync' this obj' $mapplied |]
                      in if ident `M.member` formalParams
                         then maybeWrapThis [hs| (I'.lift . I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n)) =<< (($mwrapped) $(HS.Var $ HS.UnQual $ HS.Ident calleeVar)) |]
                         else maybeWrapThis [hs| (I'.lift . I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n)) =<< (($mwrapped) =<< I'.lift (I'.readIORef $(HS.Var $ HS.UnQual $ HS.Ident calleeVar))) |]
                 else let mapplied = runReader (let ?vars = localVars in foldlM
                                                         (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs| $acc <*> $targ |])
                                                         [hs| I'.pure $(HS.Var $ HS.UnQual $ HS.Ident mname) |]
                                                         args) formalParams
                          mwrapped = HS.Lambda noLoc [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs| sync' this obj' =<< I'.lift ($mapplied) |]
                      in if ident `M.member` formalParams
                         then maybeWrapThis [hs| (I'.lift . I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n)) =<< (($mwrapped) $(HS.Var $ HS.UnQual $ HS.Ident calleeVar)) |]
                         else maybeWrapThis [hs| (I'.lift . I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n)) =<< (($mwrapped) =<< I'.lift (I'.readIORef $(HS.Var $ HS.UnQual $ HS.Ident calleeVar))) |] ]
      Just _ ->  errorPos p "caller variable not of interface type"
      Nothing -> if ident `M.member` ?fields
                then tAss a typ i (ABS.ExpE (ABS.SyncMethCall (ABS.EThis ident) (ABS.L (p,mname)) args)) -- rewrite it to this.var
                else errorPos p "cannot find variable"
   ABS.EThis ident@(ABS.L (p,calleeVar)) ->
     case M.lookup ident ?fields of
      Just (ABS.TSimple qu) -> do -- only interface type
          scopeLevels <- get
          (locals,fields,hasForeigns) <- unzip3 <$> mapM depends args
          let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
              (prefix, iident) = splitQU qu
              iname = (if null prefix then HS.UnQual else HS.Qual $ HS.ModuleName prefix) $ HS.Ident iident
              fieldFun = HS.Var $ HS.UnQual $ HS.Ident $ calleeVar ++ "'" ++ ?cname
          pure [ HS.Qualifier $
            if null (concat locals) && not (or hasForeigns)
            then let mapplied = runReader (let ?tyvars = [] in foldlM
                                                         (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                         (HS.Var $ HS.UnQual $ HS.Ident mname) args) formalParams

                     mwrapped = HS.Lambda noLoc [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs| sync' this obj' $mapplied |]
                 in [hs| (\ this'' -> (I'.lift . I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n)) =<< ($mwrapped ($fieldFun this''))) =<< I'.lift (I'.readIORef this') |]
            else let mapplied = runReader (let ?vars = localVars in foldlM
                                                    (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs| $acc <*> $targ |])
                                                    [hs| I'.pure $(HS.Var $ HS.UnQual $ HS.Ident mname) |]                                                    
                                                    args) formalParams
                     mwrapped = HS.Lambda noLoc [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs| sync' this obj' =<< I'.lift ($mapplied) |]
                  in [hs| (\ this'' -> (I'.lift . I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n)) =<< ($mwrapped ($fieldFun this''))) =<< I'.lift/ (I'.readIORef this') |] ]
      Just _ -> errorPos p "caller field not of interface type"
      Nothing -> errorPos p "no such field"
   ABS.ELit ABS.LNull -> errorPos p "null cannot be the object callee"
   _ -> errorPos p "current compiler limitation: the object callee cannot be an arbitrary pure-exp"

tAss _ _ (ABS.L (_,n)) (ABS.ExpE (ABS.ThisSyncMethCall (ABS.L (_,mname)) args)) = do
  scopeLevels <- get
  (locals,fields,hasForeigns) <- unzip3 <$> mapM depends args
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
  pure [HS.Qualifier $
         if null (concat locals) && not (or hasForeigns)
         then let mapplied = runReader (let ?tyvars = [] in foldlM
                                                      (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                      (HS.Var $ HS.UnQual $ HS.Ident $ if mname `elem` ?cAloneMethods
                                                                                       then mname ++ "''" ++ ?cname -- alone-method
                                                                                       else mname)
                                                      args) formalParams
                  maybeWrapThis = if null (concat fields) then id else (\ e -> [hs| (\ this'' -> $e) =<< I'.lift (I'.readIORef this')|])
                  ioAction = [hs| (this <..> $mapplied)|]
              in [hs| (I'.lift . I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n)) =<< $(maybeWrapThis ioAction) |]
         else let mapplied = runReader (let ?vars = localVars in foldlM
                                                 (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs| $acc <*> $targ |])
                                                 ((\ e-> [hs|I'.pure $e|]) (HS.Var $ HS.UnQual $ HS.Ident $ if mname `elem` ?cAloneMethods
                                                                                                           then mname ++ "''" ++ ?cname -- alone-method
                                                                                                           else mname))
                                                 args) formalParams
                  maybeWrapThis = if null (concat fields) then id else (\ e -> [hs| (\ this'' -> $e) =<< I'.readIORef this'|])
              in [hs| (I'.lift . I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n)) =<< ((this <..>) =<< I'.lift $(maybeWrapThis mapplied)) |] ]

tAss a typ i@(ABS.L (_,n)) (ABS.ExpE (ABS.AsyncMethCall pexp (ABS.L (p,mname)) args)) =
 case pexp of
  ABS.EVar ident@(ABS.L (_, calleeVar)) -> do
    scopeLevels <- get
    case M.lookup ident $ M.unions scopeLevels of -- check type in the scopes
      Just (ABS.TSimple qu) -> do -- only interface type
          (locals,fields,hasForeigns) <- unzip3 <$> mapM depends args
          let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
              maybeWrapThis = if null (concat fields) then id else (\ e -> [hs| (\ this'' -> $e) =<< I'.readIORef this'|])
              maybeLift = if ?isInit then id else (\e -> [hs| I'.lift ($e)|])
              (prefix, iident) = splitQU qu
              iname = (if null prefix then HS.UnQual else HS.Qual $ HS.ModuleName prefix) $ HS.Ident iident
          pure [HS.Qualifier $
                 if null (concat locals) && not (or hasForeigns)
                 then let mapplied = runReader (let ?tyvars = [] in foldlM
                                                         (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                         (HS.Var $ HS.UnQual $ HS.Ident mname) args) formalParams
                          mwrapped = HS.Lambda noLoc [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs| (obj' <!> $mapplied) |]
                      in maybeLift $ maybeWrapThis $ if ident `M.member` formalParams
                                     then [hs| I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n) =<< (($mwrapped) $(HS.Var $ HS.UnQual $ HS.Ident calleeVar)) |]
                                     else [hs| I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n) =<< (($mwrapped) =<< I'.readIORef $(HS.Var $ HS.UnQual $ HS.Ident calleeVar)) |]
                 else let mapplied = runReader (let ?vars = localVars in foldlM
                                                                            (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs| $acc <*> $targ |])
                                                                            [hs| I'.pure $(HS.Var $ HS.UnQual $ HS.Ident mname) |]
                                                                            args) formalParams
                          mwrapped = HS.Lambda noLoc [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs| (obj' <!>) =<< $mapplied |]
                      in maybeLift $ if ident `M.member` formalParams
                         then [hs| I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n) =<< (($(maybeWrapThis mwrapped)) $(HS.Var $ HS.UnQual $ HS.Ident calleeVar)) |] 
                         else [hs| I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n) =<< (($(maybeWrapThis mwrapped)) =<< I'.readIORef $(HS.Var $ HS.UnQual $ HS.Ident calleeVar)) |] ]
      Nothing -> if ident `M.member` ?fields
                then tAss a typ i (ABS.ExpE (ABS.AsyncMethCall (ABS.EThis ident) (ABS.L (p,mname)) args)) -- rewrite it to this.var
                else errorPos p "cannot find variable"
      _ -> errorPos p "invalid object callee type"
  ABS.EThis ident@(ABS.L (p,calleeVar)) ->
    case M.lookup ident ?fields of
      Just (ABS.TSimple qu) -> do -- only interface type
          scopeLevels <- get
          (locals,fields,hasForeigns) <- unzip3 <$> mapM depends args
          let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
              (prefix, iident) = splitQU qu
              iname = (if null prefix then HS.UnQual else HS.Qual $ HS.ModuleName prefix) $ HS.Ident iident
              fieldFun = HS.Var $ HS.UnQual $ HS.Ident $ calleeVar ++ "'" ++ ?cname
              maybeLift = if ?isInit then id else (\e -> [hs| I'.lift ($e)|])
          pure [HS.Qualifier $ 
            if null (concat locals) && not (or hasForeigns)
            then let mapplied = runReader (let ?tyvars = [] in foldlM
                                                         (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                         (HS.Var $ HS.UnQual $ HS.Ident mname) args) formalParams
                     mwrapped = HS.Lambda noLoc [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs| (obj' <!> $mapplied) |]
                 in maybeLift [hs| (\ this'' -> I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n) =<< ($mwrapped ($fieldFun this''))) =<< I'.readIORef this' |]
            else let mapplied = runReader (let ?vars = localVars in foldlM
                                                    (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs| $acc <*> $targ |])
                                                    [hs| I'.pure $(HS.Var $ HS.UnQual $ HS.Ident mname) |]                                                    
                                                    args) formalParams
                     mwrapped = HS.Lambda noLoc [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs| (obj' <!>) =<< $mapplied |]
                 in maybeLift [hs| (\ this'' -> I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n) =<< ($mwrapped ($fieldFun this''))) =<< I'.readIORef this' |] ]
      Just _ -> errorPos p "caller field not of interface type"
      Nothing -> errorPos p "no such field"
  ABS.ELit ABS.LNull -> errorPos p "null cannot be the object callee"
  _ -> errorPos p "current compiler limitation: the object callee cannot be an arbitrary pure-exp"

tAss _ _ (ABS.L (_,n)) (ABS.ExpE (ABS.ThisAsyncMethCall (ABS.L (_,mname)) args)) = do
  scopeLevels <- get
  (locals,fields,hasForeigns) <- unzip3 <$> mapM depends args
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
      maybeWrapThis = if null (concat fields) then id else (\ e -> [hs| (\ this'' -> $e) =<< I'.readIORef this'|])
      maybeLift = if ?isInit then id else (\e -> [hs| I'.lift ($e)|])
  pure [HS.Qualifier $
         if null (concat locals) && not (or hasForeigns)
         then let mapplied = runReader (let ?tyvars = [] in foldlM
                                               (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                               (HS.Var $ HS.UnQual $ HS.Ident $ if mname `elem` ?cAloneMethods
                                                                                then mname ++ "''" ++ ?cname -- alone-method
                                                                                else mname)
                                               args) formalParams
              in maybeLift $ maybeWrapThis [hs| (I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n) =<< (this <!> $mapplied)) |]
         else let mapplied = runReader (let ?vars = localVars in foldlM
                                                                      (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs| $acc <*> $targ |])
                                                                      ((\ e-> [hs|I'.pure $e|]) (HS.Var $ HS.UnQual $ HS.Ident $ if mname `elem` ?cAloneMethods
                                                                                                           then mname ++ "''" ++ ?cname -- alone-method
                                                                                                           else mname))
                                                                      args) formalParams
              in maybeLift [hs| I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n) =<< ((this <!>) =<< $(maybeWrapThis mapplied)) |] ]

tAss _ _ (ABS.L (_,n)) (ABS.ExpE (ABS.Get pexp)) = do
  scopeLevels <- get
  (locals,fields,hasForeigns) <- depends pexp
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
      maybeWrapThis = if null fields then id else (\ e -> [hs| (\ this'' -> $e) =<< I'.readIORef this'|])
      sureLift = if ?isInit then error "get not allowed inside init" else (\e -> [hs| I'.lift ($e)|])
  pure [HS.Qualifier $
         if null locals && not hasForeigns
         then let texp = runReader (let ?tyvars = [] in tPureExp pexp) formalParams
              in sureLift $ maybeWrapThis [hs| I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n) =<< get $texp |]
         else let texp = runReader (let ?vars = localVars in tStmExp pexp) formalParams
              in sureLift [hs| I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n) =<< (get =<< $(maybeWrapThis texp))|] ]

tAss _ _ (ABS.L (_,n)) (ABS.ExpE (ABS.ProTry pexp)) = do
  scopeLevels <- get
  (locals,fields,hasForeigns) <- depends pexp
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
      maybeWrapThis = if null fields then id else (\ e -> [hs| (\ this'' -> $e) =<< I'.readIORef this'|])
      maybeLift = if ?isInit then id else (\e -> [hs| I'.lift ($e)|])
  pure [HS.Qualifier $
         if null locals && not hasForeigns
         then let texp = runReader (let ?tyvars = [] in tPureExp pexp) formalParams
              in maybeLift $ maybeWrapThis [hs| I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n) =<< pro_try $texp |]
         else let texp = runReader (let ?vars = localVars in tStmExp pexp) formalParams
              in maybeLift [hs| I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n) =<< (pro_try =<< $(maybeWrapThis texp)) |] ]

tAss _ _ (ABS.L (_,n)) (ABS.ExpE ABS.ProNew) = do
  let maybeLift = if ?isInit then id else (\e -> [hs| I'.lift ($e)|])
  pure [HS.Qualifier $ maybeLift [hs| I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n) =<< pro_new |] ]


------------- DECLARATION+LOCAL VARIABLE ASSIGNMENT

tStm (ABS.AnnStm _ (ABS.SDecAss t i@(ABS.L (_,n)) (ABS.ExpP pexp))) = do
  scopeLevels <- addToScope t i
  (locals, fields,hasForeigns) <- depends pexp
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
      maybeWrapThis = if null fields then id else (\ e -> [hs| (\ this'' -> $e) =<< I'.readIORef this'|])
      maybeLift = if ?isInit then id else (\e -> [hs| I'.lift ($e)|])
  pure [HS.Generator noLoc 
        (HS.PatTypeSig noLoc (HS.PVar $ HS.Ident n) (HS.TyApp (HS.TyCon $ HS.UnQual $ HS.Ident "IORef'") (tType t))) $
         if null locals && not hasForeigns
         then let texp = runReader (let ?tyvars = [] in tPureExp pexp) formalParams
              in maybeLift $ maybeWrapThis [hs| I'.newIORef $texp |]
         else let texp = runReader (let ?vars = localVars in tStmExp pexp) formalParams
              in maybeLift [hs| I'.newIORef =<< $(maybeWrapThis texp) |] ]


tStm (ABS.AnnStm _ (ABS.SDecAss t@(ABS.TSimple qu) i@(ABS.L (_,n)) (ABS.ExpE (ABS.New qcname args)))) = do
  scopeLevels <- addToScope t i
  (locals,fields,hasForeigns) <- unzip3 <$> mapM depends args
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
      maybeWrapThis = if null (concat fields) then id else (\ e -> [hs| (\ this'' -> $e) =<< I'.readIORef this'|])
      maybeLift = if ?isInit then id else (\e -> [hs| I'.lift ($e)|])
      (q, cname) = splitQU qcname
      smartCon = HS.Var $ (if null q then HS.UnQual else HS.Qual $ HS.ModuleName q) $ HS.Ident $ "smart'" ++ cname
      initFun = HS.Var $ (if null q then HS.UnQual else HS.Qual $ HS.ModuleName q) $ HS.Ident $ "init'" ++ cname
  pure [HS.Generator noLoc 
        (HS.PatTypeSig noLoc (HS.PVar $ HS.Ident n) (HS.TyApp (HS.TyCon $ HS.UnQual $ HS.Ident "IORef'") (tType t))) $ -- typed
         if null (concat locals) && not (or hasForeigns)
         then let smartApplied = runReader (let ?tyvars = [] in foldlM
                                           (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                           smartCon
                                           args) formalParams
              in maybeLift $ maybeWrapThis [hs| ((I'.newIORef . $(HS.Var $ HS.UnQual $ HS.Ident $ showQU qu)) =<< new $initFun $smartApplied) |]
         else let smartApplied = runReader (let ?vars = localVars in foldlM
                                               (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs| $acc <*> $targ |])
                                               [hs| I'.pure $smartCon |]
                                               args) formalParams
              in maybeLift [hs| (I'.newIORef . $(HS.Var $ HS.UnQual $ HS.Ident $ showQU qu)) =<< (new $initFun =<< $(maybeWrapThis smartApplied)) |] ]

tStm (ABS.AnnStm _ (ABS.SDecAss t@(ABS.TSimple qu) i@(ABS.L (_,n)) (ABS.ExpE (ABS.NewLocal qcname args)))) = do
  scopeLevels <- addToScope t i
  (locals,fields,hasForeigns) <- unzip3 <$> mapM depends args
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
      maybeWrapThis = if null (concat fields) then id else (\ e -> [hs| (\ this'' -> $e) =<< I'.readIORef this'|])
      (q, cname) = splitQU qcname
      smartCon = HS.Var $ (if null q then HS.UnQual else HS.Qual $ HS.ModuleName q) $ HS.Ident $ "smart'" ++ cname
      initFun = HS.Var $ (if null q then HS.UnQual else HS.Qual $ HS.ModuleName q) $ HS.Ident $ "init'" ++ cname
      maybeLift = if ?isInit then id else (\e -> [hs| I'.lift ($e)|])
  pure [HS.Generator noLoc 
        (HS.PatTypeSig noLoc (HS.PVar $ HS.Ident n) (HS.TyApp (HS.TyCon $ HS.UnQual $ HS.Ident "IORef'") (tType t))) $ -- typed
         if null (concat locals) && not (or hasForeigns)
         then let smartApplied = runReader (let ?tyvars = [] in foldlM
                                           (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                           smartCon
                                           args) formalParams
              in maybeLift $ maybeWrapThis [hs| ((I'.newIORef . $(HS.Var $ HS.UnQual $ HS.Ident $ showQU qu)) =<< newlocal' this $initFun $smartApplied) |]
         else let smartApplied = runReader (let ?vars = localVars in foldlM
                                               (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs| $acc <*> $targ |])
                                               [hs| I'.pure $smartCon |]
                                               args) formalParams
              in maybeLift [hs| (I'.newIORef . $(HS.Var $ HS.UnQual $ HS.Ident $ showQU qu)) =<< (newlocal' this $initFun =<< $(maybeWrapThis smartApplied)) |] ]


tStm (ABS.AnnStm a (ABS.SDecAss t i@(ABS.L (_,n)) (ABS.ExpE (ABS.SyncMethCall pexp (ABS.L (p,mname)) args)))) =
  case pexp of
   ABS.EVar ident@(ABS.L (_, calleeVar)) -> do
    typ <- M.lookup ident . M.unions <$> get -- check type in the scopes
    case typ of
      Just (ABS.TSimple qtyp) -> do -- only interface type
          scopeLevels <- addToScope t i
          (locals,fields,hasForeigns) <- unzip3 <$> mapM depends args
          let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
              maybeWrapThis = if null (concat fields) then id else (\ e -> [hs| (\ this'' -> $e) =<< I'.lift (I'.readIORef this')|])
              (prefix, iident) = splitQU qtyp
              iname = (if null prefix then HS.UnQual else HS.Qual $ HS.ModuleName prefix) $ HS.Ident iident
          pure [HS.Generator noLoc 
                (HS.PatTypeSig noLoc (HS.PVar $ HS.Ident n) (HS.TyApp (HS.TyCon $ HS.UnQual $ HS.Ident "IORef'") (tType t))) $
                 if null (concat locals) && not (or hasForeigns)
                 then let mapplied = runReader (let ?tyvars = [] in foldlM
                                                              (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                              (HS.Var $ HS.UnQual $ HS.Ident mname)
                                                              args) formalParams
                          mwrapped = HS.Lambda noLoc [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs| sync' this obj' $mapplied |]
                      in if ident `M.member` formalParams
                         then maybeWrapThis [hs| (I'.lift . I'.newIORef) =<< (($mwrapped) $(HS.Var $ HS.UnQual $ HS.Ident calleeVar)) |]
                         else maybeWrapThis [hs| (I'.lift . I'.newIORef) =<< (($mwrapped) =<< I'.lift (I'.readIORef $(HS.Var $ HS.UnQual $ HS.Ident calleeVar))) |]
                 else let mapplied = runReader (let ?vars = localVars in foldlM
                                                         (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs| $acc <*> $targ |])
                                                         [hs| I'.pure $(HS.Var $ HS.UnQual $ HS.Ident mname) |]
                                                         args) formalParams
                          mwrapped = HS.Lambda noLoc [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs| sync' this obj' =<< I'.lift ($mapplied) |]
                      in if ident `M.member` formalParams
                         then maybeWrapThis [hs| (I'.lift . I'.newIORef) =<< (($mwrapped) $(HS.Var $ HS.UnQual $ HS.Ident calleeVar)) |]
                         else maybeWrapThis [hs| (I'.lift . I'.newIORef) =<< (($mwrapped) =<< I'.lift (I'.readIORef $(HS.Var $ HS.UnQual $ HS.Ident calleeVar))) |] ]
      Just _ ->  errorPos p "caller variable not of interface type"
      Nothing -> if ident `M.member` ?fields
                then tStm (ABS.AnnStm a (ABS.SDecAss t i (ABS.ExpE (ABS.AsyncMethCall (ABS.EThis ident) (ABS.L (p,mname)) args)))) -- rewrite it to this.var
                else errorPos p "cannot find variable"
   ABS.EThis ident@(ABS.L (p,calleeVar)) ->
     case M.lookup ident ?fields of
      Just (ABS.TSimple qu) -> do -- only interface type
          scopeLevels <- addToScope t i
          (locals,fields,hasForeigns) <- unzip3 <$> mapM depends args
          let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
              (prefix, iident) = splitQU qu
              iname = (if null prefix then HS.UnQual else HS.Qual $ HS.ModuleName prefix) $ HS.Ident iident
              fieldFun = HS.Var $ HS.UnQual $ HS.Ident $ calleeVar ++ "'" ++ ?cname
          pure [HS.Generator noLoc 
                (HS.PatTypeSig noLoc (HS.PVar $ HS.Ident n) (HS.TyApp (HS.TyCon $ HS.UnQual $ HS.Ident "IORef'") (tType t))) $
            if null (concat locals) && not (or hasForeigns)
            then let mapplied = runReader (let ?tyvars = [] in foldlM
                                                         (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                         (HS.Var $ HS.UnQual $ HS.Ident mname) args) formalParams

                     mwrapped = HS.Lambda noLoc [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs| sync' this obj' $mapplied |]
                 in [hs| (\ this'' -> (I'.lift . I'.newIORef) =<< ($mwrapped ($fieldFun this''))) =<< I'.lift (I'.readIORef this') |]
            else let mapplied = runReader (let ?vars = localVars in foldlM
                                                    (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs| $acc <*> $targ |])
                                                    [hs| I'.pure $(HS.Var $ HS.UnQual $ HS.Ident mname) |]                                                    
                                                    args) formalParams
                     mwrapped = HS.Lambda noLoc [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs| sync' this obj' =<< I'.lift ($mapplied) |]
                  in [hs| (\ this'' -> (I'.lift . I'.newIORef) =<< ($mwrapped ($fieldFun this''))) =<< I'.lift (I'.readIORef this') |] ]
      Just _ -> errorPos p "caller field not of interface type"
      Nothing -> errorPos p "no such field"
   ABS.ELit ABS.LNull -> errorPos p "null cannot be the object callee"
   _ -> errorPos p "current compiler limitation: the object callee cannot be an arbitrary pure-exp"

tStm (ABS.AnnStm _ (ABS.SDecAss t i@(ABS.L (_,n)) (ABS.ExpE (ABS.ThisSyncMethCall (ABS.L (_,mname)) args)))) = do
  scopeLevels <- addToScope t i
  (locals,fields,hasForeigns) <- unzip3 <$> mapM depends args
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
  pure [HS.Generator noLoc 
        (HS.PatTypeSig noLoc (HS.PVar $ HS.Ident n) (HS.TyApp (HS.TyCon $ HS.UnQual $ HS.Ident "IORef'") (tType t))) $
         if null (concat locals) && not (or hasForeigns)
         then let mapplied = runReader (let ?tyvars = [] in foldlM
                                                      (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                      (HS.Var $ HS.UnQual $ HS.Ident $ if mname `elem` ?cAloneMethods
                                                                                       then mname ++ "''" ++ ?cname -- alone-method
                                                                                       else mname)
                                                      args) formalParams
                  maybeWrapThis = if null (concat fields) then id else (\ e -> [hs| (\ this'' -> $e) =<< I'.lift (I'.readIORef this')|])
                  ioAction = [hs| (this <..> $mapplied) |]
              in [hs| (I'.lift . I'.newIORef) =<< $(maybeWrapThis ioAction) |]
         else let mapplied = runReader (let ?vars = localVars in foldlM
                                                 (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs| $acc <*> $targ |])
                                                 ((\ e-> [hs|I'.pure $e|]) (HS.Var $ HS.UnQual $ HS.Ident $ if mname `elem` ?cAloneMethods
                                                                                                           then mname ++ "''" ++ ?cname -- alone-method
                                                                                                           else mname))
                                                 args) formalParams
                  maybeWrapThis = if null (concat fields) then id else (\ e -> [hs| (\ this'' -> $e) =<< I'.readIORef this'|])
              in [hs| (I'.lift . I'.newIORef) =<< ((this <..>) =<< I'.lift $(maybeWrapThis mapplied)) |] ]

tStm (ABS.AnnStm a (ABS.SDecAss t i@(ABS.L (_,n)) (ABS.ExpE (ABS.AsyncMethCall pexp (ABS.L (p,mname)) args)))) =
 case pexp of
  ABS.EVar ident@(ABS.L (_,calleeVar)) -> do
    typ <- M.lookup ident . M.unions <$> get -- check type in the scopes
    case typ of
      Just (ABS.TSimple qu) -> do -- only interface type
          scopeLevels <- addToScope t i
          (locals,fields,hasForeigns) <- unzip3 <$> mapM depends args
          let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
              maybeWrapThis = if null (concat fields) then id else (\ e -> [hs| (\ this'' -> $e) =<< I'.readIORef this'|])
              maybeLift = if ?isInit then id else (\e -> [hs| I'.lift ($e)|])
              (prefix, iident) = splitQU qu
              iname = (if null prefix then HS.UnQual else HS.Qual $ HS.ModuleName prefix) $ HS.Ident iident
          pure [HS.Generator noLoc 
                (HS.PatTypeSig noLoc (HS.PVar $ HS.Ident n) (HS.TyApp (HS.TyCon $ HS.UnQual $ HS.Ident "IORef'") (tType t))) $
                 if null (concat locals) && not (or hasForeigns)
                 then let mapplied = runReader (let ?tyvars = [] in foldlM
                                                         (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                         (HS.Var $ HS.UnQual $ HS.Ident mname) args) formalParams
                          mwrapped = HS.Lambda noLoc [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs| (obj' <!> $mapplied) |]
                      in maybeLift $ maybeWrapThis $ if ident `M.member` formalParams
                                     then [hs| I'.newIORef =<< (($mwrapped) $(HS.Var $ HS.UnQual $ HS.Ident calleeVar)) |]
                                     else [hs| I'.newIORef =<< (($mwrapped) =<< I'.readIORef $(HS.Var $ HS.UnQual $ HS.Ident calleeVar)) |]
                 else let mapplied = runReader (let ?vars = localVars in foldlM 
                                                                            (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs| $acc <*> $targ |])
                                                                            [hs| I'.pure $(HS.Var $ HS.UnQual $ HS.Ident mname) |]
                                                                            args) formalParams
                          mwrapped = HS.Lambda noLoc [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs| (obj' <!>) =<< $mapplied |]
                      in maybeLift $ if ident `M.member` formalParams
                         then [hs| I'.newIORef =<< (($(maybeWrapThis mwrapped)) $(HS.Var $ HS.UnQual $ HS.Ident calleeVar)) |]
                         else [hs| I'.newIORef =<< (($(maybeWrapThis mwrapped)) =<< I'.readIORef $(HS.Var $ HS.UnQual $ HS.Ident calleeVar)) |] ]
      Nothing -> if ident `M.member` ?fields
                then tStm (ABS.AnnStm a (ABS.SDecAss t i (ABS.ExpE (ABS.AsyncMethCall (ABS.EThis ident) (ABS.L (p,mname)) args)))) -- rewrite it to this.var
                else errorPos p "cannot find variable"
      _ -> errorPos p "invalid object callee type"
  ABS.EThis ident@(ABS.L (p,calleeVar)) ->
    case M.lookup ident ?fields of
      Just (ABS.TSimple qu) -> do -- only interface type
          scopeLevels <- addToScope t i
          (locals,fields,hasForeigns) <- unzip3 <$> mapM depends args
          let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
              (prefix, iident) = splitQU qu
              iname = (if null prefix then HS.UnQual else HS.Qual $ HS.ModuleName prefix) $ HS.Ident iident
              fieldFun = HS.Var $ HS.UnQual $ HS.Ident $ calleeVar ++ "'" ++ ?cname
              maybeLift = if ?isInit then id else (\e -> [hs| I'.lift ($e)|])
          pure [HS.Generator noLoc 
                (HS.PatTypeSig noLoc (HS.PVar $ HS.Ident n) (HS.TyApp (HS.TyCon $ HS.UnQual $ HS.Ident "IORef'") (tType t))) $
            if null (concat locals) && not (or hasForeigns)
            then let mapplied = runReader (let ?tyvars = [] in foldlM
                                                         (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                         (HS.Var $ HS.UnQual $ HS.Ident mname) args) formalParams
                     mwrapped = HS.Lambda noLoc [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs| (obj' <!> $mapplied) |]
                 in maybeLift [hs| (\ this'' -> I'.newIORef =<< ($mwrapped ($fieldFun this''))) =<< I'.readIORef this' |]
            else let mapplied = runReader (let ?vars = localVars in foldlM
                                                    (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs| $acc <*> $targ |])
                                                    [hs| I'.pure $(HS.Var $ HS.UnQual $ HS.Ident mname) |]                                                    
                                                    args) formalParams
                     mwrapped = HS.Lambda noLoc [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs| (obj' <!>) =<< $mapplied |]
                 in maybeLift [hs| (\ this'' -> I'.newIORef =<< ($mwrapped ($fieldFun this''))) =<< I'.readIORef this' |] ]
      Just _ -> errorPos p "caller field not of interface type"
      Nothing -> errorPos p "no such field"
  ABS.ELit ABS.LNull -> errorPos p "null cannot be the object callee"
  _ -> errorPos p "current compiler limitation: the object callee cannot be an arbitrary pure-exp"

tStm (ABS.AnnStm _ (ABS.SDecAss t i@(ABS.L (_,n)) (ABS.ExpE (ABS.ThisAsyncMethCall (ABS.L (_,mname)) args)))) = do
  scopeLevels <- addToScope t i
  (locals,fields,hasForeigns) <- unzip3 <$> mapM depends args
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
      maybeWrapThis = if null (concat fields) then id else (\ e -> [hs| (\ this'' -> $e) =<< I'.readIORef this'|])
      maybeLift = if ?isInit then id else (\e -> [hs| I'.lift ($e)|])
  pure [HS.Generator noLoc 
        (HS.PatTypeSig noLoc (HS.PVar $ HS.Ident n) (HS.TyApp (HS.TyCon $ HS.UnQual $ HS.Ident "IORef'") (tType t))) $
         if null (concat locals) && not (or hasForeigns)
         then let mapplied = runReader (let ?tyvars = [] in foldlM
                                               (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                               (HS.Var $ HS.UnQual $ HS.Ident $ if mname `elem` ?cAloneMethods
                                                                                then mname ++ "''" ++ ?cname -- alone-method
                                                                                else mname)
                                               args) formalParams
              in maybeLift $ maybeWrapThis [hs| (I'.newIORef =<< (this <!> $mapplied)) |]
         else let mapplied = runReader (let ?vars = localVars in foldlM
                                                                      (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs| $acc <*> $targ |])
                                                                      ((\ e-> [hs|I'.pure $e|]) (HS.Var $ HS.UnQual $ HS.Ident $ if mname `elem` ?cAloneMethods
                                                                                                           then mname ++ "''" ++ ?cname -- alone-method
                                                                                                           else mname))
                                                                      args) formalParams
              in maybeLift [hs| I'.newIORef =<< ((this <!>) =<< $(maybeWrapThis mapplied)) |] ]

tStm (ABS.AnnStm _ (ABS.SDecAss t i@(ABS.L (_,n)) (ABS.ExpE (ABS.Get pexp)))) = do
  scopeLevels <- addToScope t i
  (locals,fields,hasForeigns) <- depends pexp
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
      maybeWrapThis = if null fields then id else (\ e -> [hs| (\ this'' -> $e) =<< I'.readIORef this'|])
      sureLift = if ?isInit then error "get not allowed inside init" else (\e -> [hs| I'.lift ($e)|])
  pure [HS.Generator noLoc 
        (HS.PatTypeSig noLoc (HS.PVar $ HS.Ident n) (HS.TyApp (HS.TyCon $ HS.UnQual $ HS.Ident "IORef'") (tType t))) $
         if null locals && not hasForeigns
         then let texp = runReader (let ?tyvars = [] in tPureExp pexp) formalParams
              in sureLift $ maybeWrapThis [hs| I'.newIORef =<< get $texp |]
         else let texp = runReader (let ?vars = localVars in tStmExp pexp) formalParams
              in sureLift [hs| I'.newIORef =<< (get =<< $(maybeWrapThis texp)) |] ]


tStm (ABS.AnnStm _ (ABS.SDecAss t i@(ABS.L (_,n)) (ABS.ExpE (ABS.ProTry pexp)))) = do
  scopeLevels <- addToScope t i
  (locals,fields,hasForeigns) <- depends pexp
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
      maybeWrapThis = if null fields then id else (\ e -> [hs| (\ this'' -> $e) =<< I'.readIORef this'|])
      maybeLift = if ?isInit then id else (\e -> [hs| I'.lift ($e)|])
  pure [HS.Generator noLoc
        (HS.PatTypeSig noLoc (HS.PVar $ HS.Ident n) (HS.TyApp (HS.TyCon $ HS.UnQual $ HS.Ident "IORef'") (tType t))) $
         if null locals && not hasForeigns
         then let texp = runReader (let ?tyvars = [] in tPureExp pexp) formalParams
              in maybeLift $ maybeWrapThis [hs| I'.newIORef =<< pro_try $texp |]
         else let texp = runReader (let ?vars = localVars in tStmExp pexp) formalParams
              in maybeLift [hs| I'.newIORef =<< (pro_try =<< $(maybeWrapThis texp)) |] ]

tStm (ABS.AnnStm _ (ABS.SDecAss t i@(ABS.L (_,n)) (ABS.ExpE ABS.ProNew))) = do
  _ <- addToScope t i
  let maybeLift = if ?isInit then id else (\e -> [hs| I'.lift ($e)|])
  pure [HS.Generator noLoc
        (HS.PatTypeSig noLoc (HS.PVar $ HS.Ident n) (HS.TyApp (HS.TyCon $ HS.UnQual $ HS.Ident "IORef'") (tType t))) $ 
        maybeLift [hs| I'.newIORef =<< pro_new |] ]


--- DISPATCHER: LOCAL-VARIABLE OR FIELD ASSIGMENT

tStm (ABS.AnnStm a (ABS.SAss i e)) = do
  scope <- M.unions <$> get
  case M.lookup i scope of
    Just typ -> tAss a typ i e 
    Nothing -> if i `M.member` ?fields
              then tStm (ABS.AnnStm a (ABS.SFieldAss i e)) -- normalize it to fieldass
              else error "not in scope"

------------------- FIELD ASSIGNMENT


tStm (ABS.AnnStm _ (ABS.SFieldAss (ABS.L (_,field)) (ABS.ExpP pexp))) = do
  scopeLevels <- get
  (locals, _,hasForeigns) <- depends pexp
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
      maybeLift = if ?isInit then id else (\e -> [hs| I'.lift ($e)|])
  pure [HS.Qualifier $
         if null locals && not hasForeigns
         then let texp = runReader (let ?tyvars = [] in tPureExp pexp) formalParams
                  recordUpdate = HS.RecUpdate [hs| this''|] [HS.FieldUpdate (HS.UnQual $ HS.Ident $ field ++ "'" ++ ?cname) $texp]
              in maybeLift [hs| I'.writeIORef this' =<< 
                                 ((\ this'' -> $recordUpdate) <$> I'.readIORef this') |]
         else let texp = runReader (let ?vars = localVars in tStmExp pexp) formalParams
                  recordUpdate = HS.RecUpdate [hs| this''|] [HS.FieldUpdate (HS.UnQual $ HS.Ident $ field ++ "'" ++ ?cname) [hs| v' |]]
              in maybeLift [hs| I'.writeIORef this' =<<
                                 ((\ this'' -> (\ v' -> $recordUpdate) <$> $texp) =<< I'.readIORef this') |]]
  

tStm (ABS.AnnStm _ (ABS.SFieldAss i@(ABS.L (_,field)) (ABS.ExpE (ABS.New qcname args)))) = do
  scopeLevels <- get
  (locals,_,hasForeigns) <- unzip3 <$> mapM depends args
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
      (q, cname) = splitQU qcname
      smartCon = HS.Var $ (if null q then HS.UnQual else HS.Qual $ HS.ModuleName q) $ HS.Ident $ "smart'" ++ cname
      initFun = HS.Var $ (if null q then HS.UnQual else HS.Qual $ HS.ModuleName q) $ HS.Ident $ "init'" ++ cname
      Just (ABS.TSimple qtyp) = M.lookup i ?fields 
      maybeLift = if ?isInit then id else (\e -> [hs| I'.lift ($e)|])
  pure [HS.Qualifier $ 
         if null (concat locals) && not (or hasForeigns)
         then let smartApplied = runReader (let ?tyvars = [] in foldlM
                                                         (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                         smartCon
                                                         args) formalParams
                  recordUpdate = HS.RecUpdate [hs| this''|] [HS.FieldUpdate (HS.UnQual $ HS.Ident $ field ++ "'" ++ ?cname) [hs| $(HS.Var $ HS.UnQual $ HS.Ident $ showQU qtyp) v' |]]
              in maybeLift [hs| I'.writeIORef this' =<<
                                 ((\ this'' -> (\ v' -> $recordUpdate) <$> new $initFun $smartApplied) =<< I'.readIORef this') |]
         else let smartApplied = runReader (let ?vars = localVars in foldlM
                                               (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs| $acc <*> $targ |])
                                               [hs| I'.pure $smartCon |]
                                               args) formalParams
                  recordUpdate = HS.RecUpdate [hs| this''|] [HS.FieldUpdate (HS.UnQual $ HS.Ident $ field ++ "'" ++ ?cname) [hs| $(HS.Var $ HS.UnQual $ HS.Ident $ showQU qtyp) v' |]]
              in maybeLift [hs| I'.writeIORef this' =<<
                                 ((\ this'' -> (\ v' -> $recordUpdate) <$> (new $initFun =<< $smartApplied)) =<< I'.readIORef this') |]]

tStm (ABS.AnnStm _ (ABS.SFieldAss i@(ABS.L (_,field)) (ABS.ExpE (ABS.NewLocal qcname args)))) = do
  scopeLevels <- get
  (locals,_,hasForeigns) <- unzip3 <$> mapM depends args
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
      (q, cname) = splitQU qcname
      smartCon = HS.Var $ (if null q then HS.UnQual else HS.Qual $ HS.ModuleName q) $ HS.Ident $ "smart'" ++ cname
      initFun = HS.Var $ (if null q then HS.UnQual else HS.Qual $ HS.ModuleName q) $ HS.Ident $ "init'" ++ cname
      Just (ABS.TSimple qtyp) = M.lookup i ?fields 
      maybeLift = if ?isInit then id else (\e -> [hs| I'.lift ($e)|])
  pure [HS.Qualifier $ 
         if null (concat locals) && not (or hasForeigns)
         then let smartApplied = runReader (let ?tyvars = [] in foldlM
                                                         (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                         smartCon
                                                         args) formalParams
                  recordUpdate = HS.RecUpdate [hs| this''|] [HS.FieldUpdate (HS.UnQual $ HS.Ident $ field ++ "'" ++ ?cname) [hs| $(HS.Var $ HS.UnQual $ HS.Ident $ showQU qtyp) v' |]]
              in maybeLift [hs| I'.writeIORef this' =<<
                                 ((\ this'' -> (\ v' -> $recordUpdate) <$> newlocal' this $initFun $smartApplied) =<< I'.readIORef this') |]
         else let smartApplied = runReader (let ?vars = localVars in foldlM
                                               (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs| $acc <*> $targ |])
                                               [hs| I'.pure $smartCon |]
                                               args) formalParams
                  recordUpdate = HS.RecUpdate [hs| this''|] [HS.FieldUpdate (HS.UnQual $ HS.Ident $ field ++ "'" ++ ?cname) [hs| $(HS.Var $ HS.UnQual $ HS.Ident $ showQU qtyp) v' |]]
              in maybeLift [hs| I'.writeIORef this' =<<
                                 ((\ this'' -> (\ v' -> $recordUpdate) <$> (newlocal' this $initFun =<< $smartApplied)) =<< I'.readIORef this') |]]



tStm (ABS.AnnStm a (ABS.SFieldAss i@(ABS.L (_,field)) (ABS.ExpE (ABS.SyncMethCall pexp (ABS.L (p,mname)) args)))) =
  case pexp of
   ABS.EVar ident@(ABS.L (_,calleeVar)) -> do
    scopeLevels <- get
    case M.lookup ident (M.unions scopeLevels) of -- check type in the scopes
      Just (ABS.TSimple qtyp) -> do -- only interface type
          (locals,_,hasForeigns) <- unzip3 <$> mapM depends args
          let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
              (prefix, iident) = splitQU qtyp
              iname = (if null prefix then HS.UnQual else HS.Qual $ HS.ModuleName prefix) $ HS.Ident iident
              recordUpdate = HS.RecUpdate [hs| this''|] [HS.FieldUpdate (HS.UnQual $ HS.Ident $ field ++ "'" ++ ?cname) [hs| v' |]]
          pure [ HS.Qualifier $
                 if null (concat locals) && not (or hasForeigns)
                 then let mapplied = runReader (let ?tyvars = [] in foldlM
                                                              (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                              (HS.Var $ HS.UnQual $ HS.Ident mname)
                                                              args) formalParams
                          mwrapped = HS.Lambda noLoc [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs| sync' this obj' $mapplied |]
                      in if ident `M.member` formalParams
                         then [hs| (I'.lift . I'.writeIORef this') =<< 
                               (( \ this'' -> (\ v' -> $recordUpdate) <$> (($mwrapped) $(HS.Var $ HS.UnQual $ HS.Ident calleeVar)))
                                =<< I'.lift (I'.readIORef this')) |]
                         else [hs| (I'.lift . I'.writeIORef this') =<< 
                              (( \ this'' -> 
                                     (\ v' -> $recordUpdate) <$> (($mwrapped) =<< I'.lift (I'.readIORef $(HS.Var $ HS.UnQual $ HS.Ident calleeVar)))
                               ) =<< I'.lift (I'.readIORef this')) |]
                 else let mapplied = runReader (let ?vars = localVars in foldlM
                                                         (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs| $acc <*> $targ |])
                                                         [hs| I'.pure $(HS.Var $ HS.UnQual $ HS.Ident mname) |]
                                                         args) formalParams
                          mwrapped = HS.Lambda noLoc [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs| sync' this obj' =<< I'.lift ($mapplied) |]
                      in if ident `M.member` formalParams
                         then [hs| (I'.lift . I'.writeIORef this') =<< 
                               (( \ this'' -> (\ v' -> $recordUpdate) <$> (($mwrapped) $(HS.Var $ HS.UnQual $ HS.Ident calleeVar)))
                                =<< I'.lift (I'.readIORef this')) |]
                         else [hs| (I'.lift . I'.writeIORef this') =<< 
                              (( \ this'' -> 
                                     (\ v' -> $recordUpdate) <$> (($mwrapped) =<< I'.lift (I'.readIORef $(HS.Var $ HS.UnQual $ HS.Ident calleeVar)))
                               ) =<< I'.lift (I'.readIORef this')) |] ]
      Just _ ->  errorPos p "caller variable not of interface type"
      Nothing -> if ident `M.member` ?fields
                then tStm (ABS.AnnStm a (ABS.SFieldAss i (ABS.ExpE (ABS.SyncMethCall (ABS.EThis ident) (ABS.L (p,mname)) args)))) -- rewrite it to this.var
                else errorPos p "cannot find variable"
   ABS.EThis ident@(ABS.L (p,calleeVar)) ->
     case M.lookup ident ?fields of
      Just (ABS.TSimple qtyp) -> do -- only interface type
          scopeLevels <- get
          (locals,fields,hasForeigns) <- unzip3 <$> mapM depends args
          let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
              (prefix, iident) = splitQU qtyp
              iname = (if null prefix then HS.UnQual else HS.Qual $ HS.ModuleName prefix) $ HS.Ident iident
              fieldFun = HS.Var $ HS.UnQual $ HS.Ident $ calleeVar ++ "'" ++ ?cname
              recordUpdate = HS.RecUpdate [hs| this''|] [HS.FieldUpdate (HS.UnQual $ HS.Ident $ field ++ "'" ++ ?cname) [hs| v' |]]
          pure [ HS.Qualifier $
            if null (concat locals) && not (or hasForeigns)
            then let mapplied = runReader (let ?tyvars = [] in foldlM
                                                         (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                         (HS.Var $ HS.UnQual $ HS.Ident mname) args) formalParams
                     mwrapped = HS.Lambda noLoc [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs| sync' this obj' $mapplied |]
                 in [hs| (I'.lift . I'.writeIORef this') =<< ((\ this'' -> (\ v' -> $recordUpdate) <$> ($mwrapped ($fieldFun this''))) =<< I'.lift (I'.readIORef this')) |]
            else let mapplied = runReader (let ?vars = localVars in foldlM
                                                    (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs| $acc <*> $targ |])
                                                    [hs| I'.pure $(HS.Var $ HS.UnQual $ HS.Ident mname) |]                                                    
                                                    args) formalParams
                     mwrapped = HS.Lambda noLoc [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs| sync' this obj' =<< I'.lift ($mapplied) |]
                 in [hs| (I'.lift . I'.writeIORef this') =<< ((\ this'' -> (\ v' -> $recordUpdate) <$> ($mwrapped ($fieldFun this''))) =<< I'.lift (I'.readIORef this')) |] ]
      Just _ -> errorPos p "caller field not of interface type"
      Nothing -> errorPos p "no such field"
   ABS.ELit ABS.LNull -> errorPos p "null cannot be the object callee"
   _ -> errorPos p "current compiler limitation: the object callee cannot be an arbitrary pure-exp"

tStm (ABS.AnnStm _ (ABS.SFieldAss (ABS.L (_,field)) (ABS.ExpE (ABS.ThisSyncMethCall (ABS.L (_,mname)) args)))) = do
  scopeLevels <- get
  (locals,_,hasForeigns) <- unzip3 <$> mapM depends args
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
  pure [HS.Qualifier $
         if null (concat locals) && not (or hasForeigns)
         then let mapplied = runReader (let ?tyvars = [] in foldlM
                                                      (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                      (HS.Var $ HS.UnQual $ HS.Ident $ if mname `elem` ?cAloneMethods
                                                                                       then mname ++ "''" ++ ?cname -- alone-method
                                                                                       else mname)
                                                      args) formalParams
                  recordUpdate = HS.RecUpdate [hs| this''|] [HS.FieldUpdate (HS.UnQual $ HS.Ident $ field ++ "'" ++ ?cname) [hs| v' |]]
              in [hs| (I'.lift . I'.writeIORef this') =<< 
                      ((\ this'' -> (\ v' -> $recordUpdate) <$> (this <..> $mapplied)) =<< I'.lift (I'.readIORef this'))  |]
         else let mapplied = runReader (let ?vars = localVars in foldlM
                                                 (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs| $acc <*> $targ |])
                                                 ((\ e-> [hs|I'.pure $e|]) (HS.Var $ HS.UnQual $ HS.Ident $ if mname `elem` ?cAloneMethods
                                                                                                           then mname ++ "''" ++ ?cname -- alone-method
                                                                                                           else mname))
                                                 args) formalParams
                  recordUpdate = HS.RecUpdate [hs| this''|] [HS.FieldUpdate (HS.UnQual $ HS.Ident $ field ++ "'" ++ ?cname) [hs| v' |]]
              in [hs| (I'.lift . I'.writeIORef this') =<< 
                      ((\ this'' -> (\ v' -> $recordUpdate) <$> ((this <..>) =<< I'.lift ($mapplied))) =<< I'.lift (I'.readIORef this')) |]]

tStm (ABS.AnnStm a (ABS.SFieldAss i@(ABS.L (_,field)) (ABS.ExpE (ABS.AsyncMethCall pexp (ABS.L (p,mname)) args)))) =
 case pexp of
  ABS.EVar ident@(ABS.L (_, calleeVar)) -> do
    scopeLevels <- get
    case M.lookup ident $ M.unions scopeLevels of -- check type in the scopes
      Just (ABS.TSimple qtyp) -> do -- only interface type
          (locals,_,hasForeigns) <- unzip3 <$> mapM depends args
          let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
              (prefix, iident) = splitQU qtyp
              iname = (if null prefix then HS.UnQual else HS.Qual $ HS.ModuleName prefix) $ HS.Ident iident
              recordUpdate = HS.RecUpdate [hs| this''|] [HS.FieldUpdate (HS.UnQual $ HS.Ident $ field ++ "'" ++ ?cname) [hs| v' |]]
              maybeLift = if ?isInit then id else (\e -> [hs| I'.lift ($e)|])
          pure [HS.Qualifier $
                 if null (concat locals) && not (or hasForeigns)
                 then let mapplied = runReader (let ?tyvars = [] in foldlM
                                                         (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                         (HS.Var $ HS.UnQual $ HS.Ident mname) args) formalParams
                          mwrapped = HS.Lambda noLoc [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs| (obj' <!> $mapplied) |]
                      in if ident `M.member` formalParams
                         then maybeLift [hs|
                              I'.writeIORef this' =<< (\ this'' -> 
                                                        (\ v' -> $recordUpdate) <$> (($mwrapped) 
                                                                                   $(HS.Var $ HS.UnQual $ HS.Ident calleeVar))) 
                                                        =<< I'.readIORef this' |]
                         else maybeLift [hs| 
                              I'.writeIORef this' =<< (\ this'' -> 
                                                        (\ v' -> $recordUpdate) <$> (($mwrapped) 
                                                                                   =<< I'.readIORef $(HS.Var $ HS.UnQual $ HS.Ident calleeVar))) 
                                                        =<< I'.readIORef this' |]
                 else let mapplied = runReader (let ?vars = localVars in foldlM
                                                                            (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs| $acc <*> $targ |])
                                                                            [hs| I'.pure $(HS.Var $ HS.UnQual $ HS.Ident mname) |]
                                                                            args) formalParams
                          mwrapped = HS.Lambda noLoc [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs| (obj' <!>) =<< $mapplied |]
                      in maybeLift $ if ident `M.member` formalParams
                         then [hs| I'.writeIORef this' =<< (\ this'' -> 
                                                        (\ v' -> $recordUpdate) <$> (($mwrapped) 
                                                                                   $(HS.Var $ HS.UnQual $ HS.Ident calleeVar))) 
                                                        =<< I'.readIORef this' |]
                         else [hs| I'.writeIORef this' =<< (\ this'' -> 
                                                        (\ v' -> $recordUpdate) <$> (($mwrapped) 
                                                                                   =<< I'.readIORef $(HS.Var $ HS.UnQual $ HS.Ident calleeVar))) 
                                                        =<< I'.readIORef this' |]]
      Nothing -> if ident `M.member` ?fields
                then tStm (ABS.AnnStm a (ABS.SFieldAss i (ABS.ExpE (ABS.AsyncMethCall (ABS.EThis ident) (ABS.L (p,mname)) args))))
                else errorPos p "cannot find variable"
      _ -> errorPos p "invalid object callee type"
  ABS.EThis ident@(ABS.L (p,calleeVar)) ->
    case M.lookup ident ?fields of
      Just (ABS.TSimple qtyp) -> do -- only interface type
          scopeLevels <- get
          (locals,fields,hasForeigns) <- unzip3 <$> mapM depends args
          let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
              (prefix, iident) = splitQU qtyp
              iname = (if null prefix then HS.UnQual else HS.Qual $ HS.ModuleName prefix) $ HS.Ident iident
              fieldFun = HS.Var $ HS.UnQual $ HS.Ident $ calleeVar ++ "'" ++ ?cname
              recordUpdate = HS.RecUpdate [hs| this''|] [HS.FieldUpdate (HS.UnQual $ HS.Ident $ field ++ "'" ++ ?cname) [hs| v' |]]
              maybeLift = if ?isInit then id else (\e -> [hs| I'.lift ($e)|])
          pure [HS.Qualifier $
            if null (concat locals) && not (or hasForeigns)
            then let mapplied = runReader (let ?tyvars = [] in foldlM
                                                         (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                         (HS.Var $ HS.UnQual $ HS.Ident mname) args) formalParams
                     mwrapped = HS.Lambda noLoc [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs| (obj' <!> $mapplied) |]
                 in maybeLift [hs| I'.writeIORef this' =<< (\ this'' -> (\ v' -> $recordUpdate) <$> ($mwrapped ($fieldFun this''))) =<< I'.readIORef this' |]
            else let mapplied = runReader (let ?vars = localVars in foldlM
                                                    (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs| $acc <*> $targ |])
                                                    [hs| I'.pure $(HS.Var $ HS.UnQual $ HS.Ident mname) |]                                                    
                                                    args) formalParams
                     mwrapped = HS.Lambda noLoc [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs| (obj' <!>) =<< $mapplied |]
                 in maybeLift [hs| I'.writeIORef this' =<< (\ this'' -> (\ v' -> $recordUpdate) <$> ($mwrapped ($fieldFun this''))) =<< I'.readIORef this' |] ]
      Just _ -> errorPos p "caller field not of interface type"
      Nothing -> errorPos p "no such field"
  ABS.ELit ABS.LNull -> errorPos p "null cannot be the object callee"
  _ -> errorPos p "current compiler limitation: the object callee cannot be an arbitrary pure-exp"



tStm (ABS.AnnStm _ (ABS.SFieldAss (ABS.L (_,field)) (ABS.ExpE (ABS.ThisAsyncMethCall (ABS.L (_,mname)) args)))) = do
  scopeLevels <- get
  (locals,_,hasForeigns) <- unzip3 <$> mapM depends args
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
      maybeLift = if ?isInit then id else (\e -> [hs| I'.lift ($e)|])
  pure [HS.Qualifier $
         if null (concat locals) && not (or hasForeigns)
         then let mapplied = runReader (let ?tyvars = [] in foldlM
                                               (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                               (HS.Var $ HS.UnQual $ HS.Ident $ if mname `elem` ?cAloneMethods
                                                                                then mname ++ "''" ++ ?cname -- alone-method
                                                                                else mname)
                                               args) formalParams
                  recordUpdate = HS.RecUpdate [hs| this''|] [HS.FieldUpdate (HS.UnQual $ HS.Ident $ field ++ "'" ++ ?cname) [hs| v' |]]
              in maybeLift [hs| I'.writeIORef this' =<< ((\ this'' -> (\ v' -> $recordUpdate) <$> (this <!> $mapplied)) =<< I'.readIORef this') |]
         else let mapplied = runReader (let ?vars = localVars in foldlM
                                                                      (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs| $acc <*> $targ |])
                                                                      ((\ e-> [hs|I'.pure $e|]) (HS.Var $ HS.UnQual $ HS.Ident $ if mname `elem` ?cAloneMethods
                                                                                                           then mname ++ "''" ++ ?cname -- alone-method
                                                                                                           else mname))
                                                                      args) formalParams
                  recordUpdate = HS.RecUpdate [hs| this''|] [HS.FieldUpdate (HS.UnQual $ HS.Ident $ field ++ "'" ++ ?cname) [hs| v' |]]
              in maybeLift [hs| I'.writeIORef this' =<< ((\ this'' -> (\ v' -> $recordUpdate) <$> ((this <!>) =<< $mapplied)) =<< I'.readIORef this') |]]

tStm (ABS.AnnStm _ (ABS.SFieldAss (ABS.L (_,field)) (ABS.ExpE (ABS.Get pexp)))) = do
  scopeLevels <- get
  (locals,_,hasForeigns) <- depends pexp
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
      sureLift = if ?isInit then error "get not allowed inside init" else (\e -> [hs| I'.lift ($e)|])
  pure [HS.Qualifier $
         if null locals && not hasForeigns
         then let texp = runReader (let ?tyvars = [] in tPureExp pexp) formalParams
                  recordUpdate = HS.RecUpdate [hs| this''|] [HS.FieldUpdate (HS.UnQual $ HS.Ident $ field ++ "'" ++ ?cname) [hs| v' |]]
              in sureLift [hs| I'.writeIORef this' =<< ((\ this'' -> (\ v' -> $recordUpdate) <$> get $texp) =<< I'.readIORef this') |]
         else let texp = runReader (let ?vars = localVars in tStmExp pexp) formalParams
                  recordUpdate = HS.RecUpdate [hs| this''|] [HS.FieldUpdate (HS.UnQual $ HS.Ident $ field ++ "'" ++ ?cname) [hs| v' |]]
              in sureLift [hs| I'.writeIORef this' =<< ((\ this'' -> (\ v' -> $recordUpdate) <$> (get =<< $texp)) =<< I'.readIORef this') |]]

tStm (ABS.AnnStm _ (ABS.SFieldAss (ABS.L (_,field)) (ABS.ExpE (ABS.ProTry pexp)))) = do
    scopeLevels <- get
    (locals,fields,hasForeigns) <- depends pexp
    let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
        maybeLift = if ?isInit then id else (\e -> [hs| I'.lift ($e)|])
    pure [HS.Qualifier $
           if null locals && not hasForeigns
           then let texp = runReader (let ?tyvars = [] in tPureExp pexp) formalParams
                    recordUpdate = HS.RecUpdate [hs| this''|] [HS.FieldUpdate (HS.UnQual $ HS.Ident $ field ++ "'" ++ ?cname) [hs| v' |]]
                in maybeLift [hs| I'.writeIORef this' =<< ((\ this'' -> (\ v' -> $recordUpdate) <$> pro_try $texp) =<< I'.readIORef this') |]
          else let texp = runReader (let ?vars = localVars in tStmExp pexp) formalParams
                   recordUpdate = HS.RecUpdate [hs| this''|] [HS.FieldUpdate (HS.UnQual $ HS.Ident $ field ++ "'" ++ ?cname) [hs| v' |]]
                in maybeLift [hs| I'.writeIORef this' =<< ((\ this'' -> (\ v' -> $recordUpdate) <$> (pro_try =<< $texp)) =<< I'.readIORef this') |]]

tStm (ABS.AnnStm _ (ABS.SFieldAss (ABS.L (_,field)) (ABS.ExpE ABS.ProNew))) = do
    let maybeLift = if ?isInit then id else (\e -> [hs| I'.lift ($e)|])
        recordUpdate = HS.RecUpdate [hs| this''|] [HS.FieldUpdate (HS.UnQual $ HS.Ident $ field ++ "'" ++ ?cname) [hs| v' |]]
    pure [HS.Qualifier $
            maybeLift [hs| I'.writeIORef this' =<< ((\ this'' -> (\ v' -> $recordUpdate) <$> pro_new) =<< I'.readIORef this') |]]
          

------------------------- RETURN , STANDALONE EXPRESSION

tStm (ABS.AnnStm _ (ABS.SReturn (ABS.ExpE eexp))) = return . HS.Qualifier <$> tEffExp eexp False -- keep the result
tStm (ABS.AnnStm _ (ABS.SReturn (ABS.ExpP pexp))) = do
  scopeLevels <- get
  (locals, fields,hasForeigns) <- depends pexp
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
      maybeLift = if ?isInit then id else (\e -> [hs| I'.lift ($e)|])
  pure $ [HS.Qualifier $        -- keep the result
          if null locals && not hasForeigns
          then let texp = runReader (let ?tyvars = [] in tPureExp pexp) formalParams
                   maybeWrapThis = if null fields then id else (\ e -> maybeLift [hs| (\ this'' -> $e) =<< I'.readIORef this'|])
               in maybeWrapThis [hs| I'.pure $texp |]
          else let texp = runReader (let ?vars = localVars in tStmExp pexp) formalParams
                   maybeWrapThis = if null fields then id else (\ e -> [hs| (\ this'' -> $e) =<< I'.readIORef this'|])
               in maybeLift $ maybeWrapThis texp ]

tStm (ABS.AnnStm _ (ABS.SExp (ABS.ExpE eexp))) = return . HS.Generator noLoc HS.PWildCard <$> tEffExp eexp True -- throw away the result
tStm (ABS.AnnStm _ (ABS.SExp (ABS.ExpP pexp))) = do
  scopeLevels <- get
  (locals, fields,hasForeigns) <- depends pexp
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
      maybeLift = if ?isInit then id else (\e -> [hs| I'.lift ($e)|])
  pure $ [HS.Generator noLoc HS.PWildCard $ -- throw away the result
          if null locals && not hasForeigns
          then let texp = runReader (let ?tyvars = [] in tPureExp pexp) formalParams
                   maybeWrapThis = if null fields then id else (\ e -> maybeLift [hs| (\ this'' -> $e) =<< I'.readIORef this'|])
               in maybeWrapThis [hs| I'.pure $texp |]
          else let texp = runReader (let ?vars = localVars in tStmExp pexp) formalParams
                   maybeWrapThis = if null fields then id else (\ e -> [hs| (\ this'' -> $e) =<< I'.readIORef this'|])
               in maybeLift $ maybeWrapThis texp ]


---- DECLARATION

tStm (ABS.AnnStm _ (ABS.SDec t i@(ABS.L (p,n)))) = do
  _ <- addToScope t i
  let maybeLift = if ?isInit then id else (\e -> [hs| I'.lift ($e)|])
  pure $ [HS.Generator noLoc 
          (HS.PatTypeSig noLoc (HS.PVar $ HS.Ident n) (HS.TyApp (HS.TyCon $ HS.UnQual $ HS.Ident "IORef'") (tType t))) $
          case t of
            -- it is an unitialized future (set to newEmptyMVar)
            ABS.TPoly (ABS.U_ (ABS.U (_,"Fut")))  _ -> maybeLift [hs| I'.newIORef nullFuture' |]
            -- it may be an object (set to null) or foreign (set to undefined)
            _ -> let
                  qtyp = case t of
                           ABS.TSimple qtyp' -> qtyp'
                           ABS.TPoly qtyp' _ -> qtyp'
                  (prefix, ident) = splitQU qtyp
                  Just (SV symbolType _) = if null prefix
                                           then snd <$> find (\ (SN ident' modul,_) -> ident == ident' && maybe True (not . snd) modul) (M.assocs ?st)
                                           else M.lookup (SN ident (Just (prefix, True))) ?st 
                in case symbolType of
                     Interface _ _ -> maybeLift [hs| I'.newIORef ($(HS.Var $ HS.UnQual $ HS.Ident $ showQU qtyp) null) |]  -- o :: IORef Interf <- null
                     Foreign -> maybeLift [hs| I'.newIORef (I'.error "foreign object not initialized") |] -- undefined if foreign
                     _ -> errorPos p "A field must be initialised if it is not of a reference type"
         ]


-- CONCURRENCY STATEMENTS
-------------------------

tStm (ABS.AnnStm _ ABS.SSuspend) = pure [HS.Qualifier [hs| suspend this |]]

tStm (ABS.AnnStm _ (ABS.SAwait g)) = do
  let (futureGuards, boolGuards) = splitGuard g
  tfguards <- mapM tGuard futureGuards   -- sequentialize: await f1guard? ; await f2guard?;
  tbguards <- if null boolGuards
             then pure []                           
             else tGuard (foldl1 (\ (ABS.GExp exp1) (ABS.GExp exp2) -> ABS.GExp $ exp1 `ABS.EAnd` exp2) boolGuards) -- combine bguards with boolean AND
  pure $ concat tfguards
       ++ tbguards
  where
    splitGuard :: ABS.AwaitGuard -> ([ABS.AwaitGuard], [ABS.AwaitGuard])
    splitGuard g = splitGuard' g ([],[])
    splitGuard' g (fs,as)= case g of
                             ABS.GFutField _ -> (g:fs,as)
                             ABS.GFut _ -> (g:fs,as)
                             ABS.GExp _ -> (fs,g:as)
                             ABS.GAnd gl gr -> let 
                                                   (fsl,asl) = splitGuard gl
                                                   (fsr,asr) = splitGuard gr 
                                                  in (fsl++fs++fsr,asl++as++asr)

    tGuard (ABS.GFut var@(ABS.L (_, fname))) = do
      scopeLevels <- get                                 
      let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
      if var `M.member` formalParams 
        then  pure [HS.Qualifier [hs| awaitFuture' this $(HS.Var $ HS.UnQual $ HS.Ident fname) |]]
        else if var `M.member` localVars
             then pure [HS.Qualifier [hs| awaitFuture' this =<< I'.lift (I'.readIORef $(HS.Var $ HS.UnQual $ HS.Ident fname)) |]]
             else tGuard (ABS.GFutField var) -- try as field-future

    -- currently, no solution to the cosimo problem
    tGuard (ABS.GFutField (ABS.L (_, fname))) = do
      let fieldFun = HS.Var $ HS.UnQual $ HS.Ident $ fname ++ "'" ++ ?cname
      pure [HS.Qualifier [hs| (awaitFuture' this . $fieldFun) =<< I'.lift (I'.readIORef this') |]]

    tGuard (ABS.GExp pexp) = do
      (locals, fields,hasForeigns) <- depends pexp
      scopeLevels <- get
      let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
      if null fields
        then error "You are not checking for anything observable in AWAIT"
        else pure [HS.Qualifier $
                   if null locals && not hasForeigns
                   then let texp = runReader (let ?tyvars = [] in tPureExp pexp) formalParams
                        in [hs| awaitBool' this (\ this'' -> $texp) |]
                   else let texp = runReader (let ?tyvars = [] in tPureExp pexp) (M.unions scopeLevels)
                            expWrapped = foldl (\ acc (ABS.L (_, nextVar)) -> 
                                                    let nextIdent = HS.Ident nextVar 
                                                    in [hs| (\ ((nextIdent)) -> $acc) =<< I'.readIORef $(HS.Var $ HS.UnQual nextIdent)|])
                                         [hs| I'.pure (\ this'' -> $texp) |]
                                         (nub locals)
                        in [hs| awaitBool' this =<< I'.lift ($expWrapped) |]]

tStm (ABS.AnnStm _ (ABS.SGive pexp1 pexp2)) = do
  scopeLevels <- get
  (locals,fields,hasForeigns) <- depends (ABS.EAnd pexp1 pexp2)
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
      maybeWrapThis = if null fields then id else (\ e -> [hs| (\ this'' -> $e) =<< I'.readIORef this'|])
      maybeLift = if ?isInit then id else (\e -> [hs| I'.lift ($e)|])
  pure [HS.Qualifier $
         if null locals && not hasForeigns
         then let texp1 = runReader (let ?tyvars = [] in tPureExp pexp1) formalParams
                  texp2 = runReader (let ?tyvars = [] in tPureExp pexp2) formalParams
              in maybeLift $ maybeWrapThis [hs| pro_give $texp1 $texp2 |]
         else let texp1 = runReader (let ?vars = localVars in tStmExp pexp1) formalParams
                  texp2 = runReader (let ?vars = localVars in tStmExp pexp2) formalParams
              in maybeLift $ maybeWrapThis [hs| (\ e1' -> pro_give e1' =<< $texp2) =<< $texp1 |] ]


-- CONTROL FLOW STATEMENTS
--------------------------

tStm (ABS.AnnStm _ (ABS.SWhile pexp stmBody)) = do
  scopeLevels <- get
  (_, fields,_) <- depends pexp
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
      maybeWrapThis = if null fields then id else (\ e -> [hs| (\ this'' -> $e) =<< I'.readIORef this'|])
  let texp = runReader (let ?vars = localVars in tStmExp pexp) formalParams  -- only treat it as StmExp
  [HS.Qualifier tbody] <- tStm $ case stmBody of
                                  ABS.AnnStm _ (ABS.SBlock _) -> stmBody
                                  singleStm -> ABS.AnnStm [] (ABS.SBlock [singleStm]) -- if single statement, wrap it in a new DO-scope
  pure $ [HS.Qualifier $ if ?isInit
                         then [hs| while' $(maybeWrapThis texp) $tbody |] 
                         else [hs| while $(maybeWrapThis texp) $tbody |] ]

tStm (ABS.AnnStm _ (ABS.SIf pexp stmThen)) = do
  scopeLevels <- get
  (locals, fields,hasForeigns) <- depends pexp
  tthen <- (\case 
           [] -> [hs| I'.pure () |]
           [HS.Qualifier tthen'] -> tthen') <$> (tStm $ ABS.AnnStm [] $ case stmThen of
                                                        ABS.SBlock _ -> stmThen
                                                        singleStm -> ABS.SBlock [ABS.AnnStm [] singleStm]) -- if single statement, wrap it in a new DO-scope
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
  pure $ if null locals && not hasForeigns
         then let tpred = runReader (let ?tyvars = [] in tPureExp pexp) formalParams
                  maybeWrapThis = if null fields 
                                  then id 
                                  else if ?isInit 
                                       then (\ e -> [hs| (\ this'' -> $e) =<< I'.readIORef this' |])
                                       else (\ e -> [hs| (\ this'' -> $e) =<< I'.lift (I'.readIORef this') |])
              in [HS.Qualifier $ maybeWrapThis [hs| I'.when $tpred $tthen |]]
         else let tpred = runReader (let ?vars = localVars in tStmExp pexp) formalParams
                  maybeLift = if ?isInit then id else (\e -> [hs| I'.lift ($e)|])
                  maybeWrapThis = if null fields then id else (\ e -> [hs| (\ this'' -> $e) =<< I'.readIORef this' |])                 
              in [ HS.Generator noLoc (HS.PVar $ HS.Ident "when'") (maybeLift $ maybeWrapThis tpred)
                 , HS.Qualifier [hs| I'.when when' $tthen |]]

tStm (ABS.AnnStm _ (ABS.SIfElse pexp stmThen stmElse)) = do
  scopeLevels <- get
  (locals, fields,hasForeigns) <- depends pexp
  tthen <- (\case 
           [] -> [hs| I'.pure () |]
           [HS.Qualifier tthen'] -> tthen') <$> (tStm $ ABS.AnnStm [] $ case stmThen of
                                                        ABS.SBlock _ -> stmThen
                                                        singleStm -> ABS.SBlock [ABS.AnnStm [] singleStm]) -- if single statement, wrap it in a new DO-scope
  telse <- (\case 
           [] -> [hs| I'.pure () |]
           [HS.Qualifier telse'] -> telse') <$> (tStm $ ABS.AnnStm [] $ case stmElse of
                                                        ABS.SBlock _ -> stmElse
                                                        singleStm -> ABS.SBlock [ABS.AnnStm [] singleStm]) -- if single statement, wrap it in a new DO-scope
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
      
  pure $ if null locals && not hasForeigns
         then let tpred = runReader (let ?tyvars = [] in tPureExp pexp) formalParams
                  maybeWrapThis = if null fields 
                                  then id 
                                  else if ?isInit 
                                       then (\ e -> [hs| (\ this'' -> $e) =<< I'.readIORef this' |])
                                       else (\ e -> [hs| (\ this'' -> $e) =<< I'.lift (I'.readIORef this') |])
              in [HS.Qualifier $ maybeWrapThis [hs| if $tpred then $tthen else $telse |]]
         else let tpred = runReader (let ?vars = localVars in tStmExp pexp) formalParams
                  maybeLift = if ?isInit then id else (\e -> [hs| I'.lift ($e)|])
                  maybeWrapThis = if null fields then id else (\ e -> [hs| (\ this'' -> $e) =<< I'.readIORef this' |])                 
              in [ HS.Generator noLoc (HS.PVar $ HS.Ident "if'") (maybeLift $ maybeWrapThis tpred)
                 , HS.Qualifier [hs| if if' then $tthen else $telse |]]

-- OTHER STATEMENTS
--------------------------------

tStm (ABS.AnnStm _ ABS.SSkip) = pure [] -- ignore skip

tStm (ABS.AnnStm _ (ABS.SBlock astms)) = do
  modify' (M.empty:)            -- add scope-level

  tstms <- concat <$> mapM tStm astms

  modify' tail                  -- remove scope-level

  pure $ if null tstms
         then []                -- do not generate anything 
         else [HS.Qualifier $ HS.Do $ case last tstms of -- adds another DO
                       HS.Generator _ _ _ ->  tstms ++ [HS.Qualifier $ [hs| I'.pure () |]]
                       _ -> tstms]


tStm (ABS.AnnStm _ (ABS.SPrint pexp)) = do
  (locals, fields,hasForeigns) <- depends pexp
  scopeLevels <- get
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
      maybeWrapThis = if null fields then id else (\ e -> [hs| (\ this'' -> $e) =<< I'.readIORef this'|])
      maybeLift = if ?isInit then id else (\e -> [hs| I'.lift ($e)|])              
  pure [HS.Qualifier $ 
    if null locals && not hasForeigns
    then let texp = runReader (let ?tyvars = [] in tPureExp pexp) formalParams
         in maybeLift $ maybeWrapThis [hs| I'.putStrLn $texp |]
    else let texp = runReader (let ?vars = localVars in tStmExp pexp) formalParams
         in maybeLift [hs| I'.putStrLn =<< $(maybeWrapThis texp) |] ]

-- EXCEPTION STATEMENTS
-------------------------

tStm (ABS.AnnStm _ (ABS.SAssert pexp)) = do
  (locals, fields,hasForeigns) <- depends pexp
  scopeLevels <- get
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
      maybeWrapThis = if null fields then id else (\ e -> [hs| (\ this'' -> $e) =<< I'.readIORef this' |])
      maybeLift = if ?isInit then id else (\e -> [hs| I'.lift ($e)|])              
  pure [HS.Qualifier $ 
    if null locals && not hasForeigns
    then let texp = runReader (let ?tyvars = [] in tPureExp pexp) formalParams
         in maybeLift $ maybeWrapThis [hs| assert $texp |]
    else let texp = runReader (let ?vars = localVars in tStmExp pexp) formalParams
         in maybeLift [hs| assert =<< $(maybeWrapThis texp) |] ]

tStm (ABS.AnnStm _ (ABS.SThrow pexp)) = do
  (locals, fields,hasForeigns) <- depends pexp
  scopeLevels <- get
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
      maybeWrapThis = if null fields then id else (\ e -> [hs| (\ this'' -> $e) =<< I'.readIORef this'|])
  if null locals && not hasForeigns
    then do
      let texp = runReader (let ?tyvars = [] in tPureExp pexp) formalParams
      pure $ [HS.Qualifier $ maybeWrapThis [hs| throw $texp |] ]
    else do
      let texp = runReader (let ?vars = localVars in tStmExp pexp) formalParams
      pure $ [HS.Qualifier [hs| throw =<< $(maybeWrapThis texp) |] ]

tStm (ABS.AnnStm _ (ABS.STryCatchFinally try_stm cbranches mfinally)) = todo undefined


-- (EFFECTFUL) EXPRESSIONS in statement world
---------------------------------------------

tEffExp :: ( ?st::SymbolTable, ?fields :: M.Map ABS.L ABS.T, ?cname :: String, ?cAloneMethods :: [String], ?isInit :: Bool) => 
          ABS.EffExp -> Bool -> StmScope HS.Exp
tEffExp (ABS.New qcname args) _ = do
      scopeLevels <- get
      (locals,fields,hasForeigns) <- unzip3 <$> mapM depends args
      let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
          maybeWrapThis = if null (concat fields) then id else (\ e -> [hs| (\ this'' -> $e) =<< I'.readIORef this'|])
          maybeLift = if ?isInit then id else (\e -> [hs| I'.lift ($e)|]) 
          (q, cname) = splitQU qcname
          smartCon = HS.Var $ (if null q then HS.UnQual else HS.Qual $ HS.ModuleName q) $ HS.Ident $ "smart'" ++ cname
          initFun = HS.Var $ (if null q then HS.UnQual else HS.Qual $ HS.ModuleName q) $ HS.Ident $ "init'" ++ cname
      if null (concat locals) && not (or hasForeigns)
        then let smartApplied = runReader (let ?tyvars = [] in foldlM
                                                        (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                        smartCon
                                                        args) formalParams
             in pure $ maybeLift $ maybeWrapThis [hs| new $initFun $smartApplied |]
        else let smartApplied = runReader (let ?vars = localVars in foldlM
                                                   (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs| $acc <*> $targ |])
                                                   [hs| I'.pure $smartCon |]
                                                   args) formalParams
             in pure $ maybeLift [hs| new $initFun =<< $(maybeWrapThis smartApplied) |]

tEffExp (ABS.NewLocal qcname args) _ = do
      scopeLevels <- get
      (locals,fields,hasForeigns) <- unzip3 <$> mapM depends args
      let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
          maybeWrapThis = if null (concat fields) then id else (\ e -> [hs| (\ this'' -> $e) =<< I'.readIORef this'|])
          maybeLift = if ?isInit then id else (\e -> [hs| I'.lift ($e)|])
          (q, cname) = splitQU qcname
          smartCon = HS.Var $ (if null q then HS.UnQual else HS.Qual $ HS.ModuleName q) $ HS.Ident $ "smart'" ++ cname
          initFun = HS.Var $ (if null q then HS.UnQual else HS.Qual $ HS.ModuleName q) $ HS.Ident $ "init'" ++ cname
      if null (concat locals) && not (or hasForeigns)
        then let smartApplied = runReader (let ?tyvars = [] in foldlM
                                                        (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                        smartCon
                                                        args) formalParams
             in pure $ maybeLift $ maybeWrapThis [hs| newlocal' this $initFun $smartApplied |]
        else let smartApplied = runReader (let ?vars = localVars in foldlM
                                                   (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs| $acc <*> $targ |])
                                                   [hs| I'.pure $smartCon |]
                                                   args) formalParams
             in pure $ maybeLift [hs| newlocal' this $initFun =<< $(maybeWrapThis smartApplied) |]


tEffExp (ABS.SyncMethCall pexp (ABS.L (p,mname)) args) _isAlone = case pexp of
  ABS.EVar ident@(ABS.L (_,calleeVar)) -> do
    scopeLevels <- get
    case M.lookup ident (M.unions scopeLevels) of -- check type in the scopes
      Just (ABS.TSimple qtyp) -> do -- only interface type
          (locals,fields,hasForeigns) <- unzip3 <$> mapM depends args
          let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
              maybeWrapThis = if null (concat fields) then id else (\ e -> [hs| (\ this'' -> $e) =<< I'.lift (I'.readIORef this')|])
              (prefix, iident) = splitQU qtyp
              iname = (if null prefix then HS.UnQual else HS.Qual $ HS.ModuleName prefix) $ HS.Ident iident
          if null (concat locals) && not (or hasForeigns)
            then let mapplied = runReader (let ?tyvars = [] in foldlM
                                                         (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                         (HS.Var $ HS.UnQual $ HS.Ident mname)
                                                         args) formalParams
                     mwrapped = HS.Lambda noLoc [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs| sync' this obj' $mapplied |]
                 in pure $ if ident `M.member` formalParams
                           then maybeWrapThis [hs| ($mwrapped) $(HS.Var $ HS.UnQual $ HS.Ident calleeVar) |]
                           else maybeWrapThis [hs| ($mwrapped) =<< I'.lift (I'.readIORef $(HS.Var $ HS.UnQual $ HS.Ident calleeVar)) |]
            else let mapplied = runReader (let ?vars = localVars in foldlM
                                                    (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs| $acc <*> $targ |])
                                                    [hs| I'.pure $(HS.Var $ HS.UnQual $ HS.Ident mname) |]
                                                    args) formalParams
                     mwrapped = HS.Lambda noLoc [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs| sync' this obj' =<< I'.lift ($mapplied) |]
                 in pure $ if ident `M.member` formalParams
                           then maybeWrapThis [hs| ($mwrapped) $(HS.Var $ HS.UnQual $ HS.Ident calleeVar) |]
                           else maybeWrapThis [hs| ($mwrapped) =<< I'.lift (I'.readIORef $(HS.Var $ HS.UnQual $ HS.Ident calleeVar)) |]
      Just _ ->  errorPos p "caller variable not of interface type"
      Nothing -> if ident `M.member` ?fields
                then tEffExp (ABS.SyncMethCall (ABS.EThis ident) (ABS.L (p,mname)) args) _isAlone -- rewrite it to this.var
                else errorPos p "cannot find variable"
  ABS.EThis ident@(ABS.L (p,calleeVar)) ->
    case M.lookup ident ?fields of
      Just (ABS.TSimple qtyp) -> do -- only interface type
          scopeLevels <- get
          (locals,fields,hasForeigns) <- unzip3 <$> mapM depends args
          let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
              (prefix, iident) = splitQU qtyp
              iname = (if null prefix then HS.UnQual else HS.Qual $ HS.ModuleName prefix) $ HS.Ident iident
              fieldFun = HS.Var $ HS.UnQual $ HS.Ident $ calleeVar ++ "'" ++ ?cname
          if null (concat locals) && not (or hasForeigns)
            then let mapplied = runReader (let ?tyvars = [] in foldlM
                                                         (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                         (HS.Var $ HS.UnQual $ HS.Ident mname) args) formalParams
                     mwrapped = HS.Lambda noLoc [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs| sync' this obj' $mapplied |]
                 in pure [hs| (\ this'' -> $mwrapped ($fieldFun this'')) =<< I'.lift (I'.readIORef this') |]
            else let mapplied = runReader (let ?vars = localVars in foldlM
                                                    (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs| $acc <*> $targ |])
                                                    [hs| I'.pure $(HS.Var $ HS.UnQual $ HS.Ident mname) |]                                                    
                                                    args) formalParams
                     mwrapped = HS.Lambda noLoc [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs| sync' this obj' =<< I'.lift ($mapplied) |]
                 in pure [hs| (\ this'' -> $mwrapped ($fieldFun this'')) =<< I'.lift (I'.readIORef this') |]
      Just _ -> errorPos p "caller field not of interface type"
      Nothing -> errorPos p "no such field"
  ABS.ELit ABS.LNull -> errorPos p "null cannot be the object callee"
  _ -> errorPos p "current compiler limitation: the object callee cannot be an arbitrary pure-exp"

tEffExp (ABS.ThisSyncMethCall (ABS.L (_,mname)) args) _ = do
  scopeLevels <- get
  (locals,fields,hasForeigns) <- unzip3 <$> mapM depends args
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
  if null (concat locals) && not (or hasForeigns)
    then let mapplied = runReader (let ?tyvars = [] in foldlM
                                               (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                               (HS.Var $ HS.UnQual $ HS.Ident $ if mname `elem` ?cAloneMethods
                                                                                then mname ++ "''" ++ ?cname -- alone-method
                                                                                else mname)
                                               args) formalParams
             maybeWrapThis = if null (concat fields) then id else (\ e -> [hs| (\ this'' -> $e) =<< I'.lift (I'.readIORef this')|])
         in pure $ maybeWrapThis [hs| this <..> $mapplied |]
    else let mapplied = runReader (let ?vars = localVars in foldlM
                                              (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs| $acc <*> $targ |])
                                              ((\ e-> [hs|I'.pure $e|]) (HS.Var $ HS.UnQual $ HS.Ident $ if mname `elem` ?cAloneMethods
                                                                                                           then mname ++ "''" ++ ?cname -- alone-method
                                                                                                           else mname))
                                              args) formalParams
             maybeWrapThis = if null (concat fields) then id else (\ e -> [hs| (\ this'' -> $e) =<< I'.readIORef this'|])
         in pure [hs| (this <..>) =<< I'.lift $(maybeWrapThis mapplied) |]

tEffExp (ABS.AsyncMethCall pexp (ABS.L (p,mname)) args) isAlone = case pexp of
  ABS.EVar ident@(ABS.L (_,calleeVar)) -> do
    scopeLevels <- get
    case M.lookup ident (M.unions scopeLevels) of -- check type in the scopes
      Just (ABS.TSimple qtyp) -> do -- only interface type allowed
          (locals,fields,hasForeigns) <- unzip3 <$> mapM depends args
          let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
              maybeWrapThis = if null (concat fields) then id else (\ e -> [hs| (\ this'' -> $e) =<< I'.readIORef this'|])
              maybeLift = if ?isInit then id else (\e -> [hs| I'.lift ($e)|])
              (prefix, iident) = splitQU qtyp
              iname = (if null prefix then HS.UnQual else HS.Qual $ HS.ModuleName prefix) $ HS.Ident iident
          if null (concat locals) && not (or hasForeigns)
            then let mapplied = runReader (let ?tyvars = [] in foldlM
                                                         (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                         (HS.Var $ HS.UnQual $ HS.Ident mname) args) formalParams
                     mwrapped = HS.Lambda noLoc [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] $ if isAlone
                                                                                               then [hs| (obj' <!!> $mapplied) |] -- optimized, fire&forget
                                                                                               else [hs| (obj' <!> $mapplied) |]
                 in pure $ maybeLift $ if ident `M.member` formalParams
                           then [hs| ($(maybeWrapThis mwrapped)) $(HS.Var $ HS.UnQual $ HS.Ident calleeVar) |]
                           else [hs| ($(maybeWrapThis mwrapped)) =<< (I'.readIORef $(HS.Var $ HS.UnQual $ HS.Ident calleeVar)) |]
            else let mapplied = runReader (let ?vars = localVars in foldlM
                                                    (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs| $acc <*> $targ |])
                                                    [hs| I'.pure $(HS.Var $ HS.UnQual $ HS.Ident mname) |]                                                    
                                                    args) formalParams
                     mwrapped = HS.Lambda noLoc [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] $ if isAlone
                                                                                               then [hs| (obj' <!!>) =<< $mapplied |] -- optimized, fire&forget
                                                                                               else [hs| (obj' <!>) =<< $mapplied |]
                 in pure $ maybeLift $ if ident `M.member` formalParams
                           then [hs| ($(maybeWrapThis mwrapped)) $(HS.Var $ HS.UnQual $ HS.Ident calleeVar) |]
                           else [hs| ($(maybeWrapThis mwrapped)) =<< (I'.readIORef $(HS.Var $ HS.UnQual $ HS.Ident calleeVar)) |]
      Just _ ->  errorPos p "caller variable not of interface type"
      Nothing -> if ident `M.member` ?fields
                then tEffExp (ABS.AsyncMethCall (ABS.EThis ident) (ABS.L (p,mname)) args) isAlone -- rewrite it to this.var
                else errorPos p "cannot find variable"
  ABS.EThis ident@(ABS.L (p,calleeVar)) ->
    case M.lookup ident ?fields of
      Just (ABS.TSimple qtyp) -> do -- only interface type
          scopeLevels <- get
          (locals,fields,hasForeigns) <- unzip3 <$> mapM depends args
          let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
              (prefix, iident) = splitQU qtyp
              iname = (if null prefix then HS.UnQual else HS.Qual $ HS.ModuleName prefix) $ HS.Ident iident
              fieldFun = HS.Var $ HS.UnQual $ HS.Ident $ calleeVar ++ "'" ++ ?cname
              maybeLift = if ?isInit then id else (\e -> [hs| I'.lift ($e)|])
          if null (concat locals) && not (or hasForeigns)
            then let mapplied = runReader (let ?tyvars = [] in foldlM
                                                         (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                         (HS.Var $ HS.UnQual $ HS.Ident mname) args) formalParams
                     mwrapped = HS.Lambda noLoc [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] $ if isAlone
                                                                                               then [hs| (obj' <!!> $mapplied) |] -- optimized, fire&forget
                                                                                               else [hs| (obj' <!> $mapplied) |]
                 in pure $ maybeLift [hs| (\ this'' -> $mwrapped ($fieldFun this'')) =<< I'.readIORef this' |]
            else let mapplied = runReader (let ?vars = localVars in foldlM
                                                    (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs| $acc <*> $targ |])
                                                    [hs| I'.pure $(HS.Var $ HS.UnQual $ HS.Ident mname) |]                                                    
                                                    args) formalParams
                     mwrapped = HS.Lambda noLoc [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] $ if isAlone
                                                                                               then [hs| (obj' <!!>) =<< $mapplied |] -- optimized, fire&forget
                                                                                               else [hs| (obj' <!>) =<< $mapplied |]
                 in pure $ maybeLift [hs| (\ this'' -> $mwrapped ($fieldFun this'')) =<< I'.readIORef this' |]
      Just _ -> errorPos p "caller field not of interface type"
      Nothing -> errorPos p "no such field"
  ABS.ELit ABS.LNull -> errorPos p "null cannot be the object callee"
  _ -> errorPos p "current compiler limitation: the object callee cannot be an arbitrary pure-exp"
  
tEffExp (ABS.ThisAsyncMethCall (ABS.L (_,mname)) args) isAlone = do
  scopeLevels <- get
  (locals,fields,hasForeigns) <- unzip3 <$> mapM depends args
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
      maybeWrapThis = if null (concat fields) then id else (\ e -> [hs| (\ this'' -> $e) =<< I'.readIORef this'|])
      maybeLift = if ?isInit then id else (\e -> [hs| I'.lift ($e)|])
  if null (concat locals) && not (or hasForeigns)
    then let mapplied = runReader (let ?tyvars = [] in foldlM
                                               (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                               (HS.Var $ HS.UnQual $ HS.Ident $ if mname `elem` ?cAloneMethods
                                                                                then mname ++ "''" ++ ?cname -- alone-method
                                                                                else mname)
                                               args) formalParams
          in pure $ maybeLift $ maybeWrapThis $ if isAlone 
                        then [hs| (this <!!> $mapplied) |] -- optimized, fire&forget
                        else [hs| (this <!> $mapplied) |]
    else let mapplied = runReader (let ?vars = localVars in foldlM
                                            (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs| $acc <*> $targ |])
                                            ((\ e-> [hs|I'.pure $e|]) (HS.Var $ HS.UnQual $ HS.Ident $ if mname `elem` ?cAloneMethods
                                                                                                           then mname ++ "''" ++ ?cname -- alone-method
                                                                                                           else mname))
                                            args) formalParams
         in pure $ maybeLift $ if isAlone 
                   then [hs| (this <!!>) =<< $(maybeWrapThis mapplied) |] -- optimized, fire&forget
                   else [hs| (this <!>) =<< $(maybeWrapThis mapplied) |]

tEffExp (ABS.Get pexp) _ = do
  scopeLevels <- get
  (locals,fields,hasForeigns) <- depends pexp
  let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
      maybeWrapThis = if null fields then id else (\ e -> [hs| (\ this'' -> $e) =<< I'.readIORef this'|])
      sureLift = if ?isInit then error "get not allowed inside init" else (\e -> [hs| I'.lift ($e)|])
  if null locals && not hasForeigns
    then let texp = runReader (let ?tyvars = [] in tPureExp pexp) formalParams
         in pure $ sureLift $ maybeWrapThis [hs| get $texp |]
    else let texp = runReader (let ?vars = localVars in tStmExp pexp) formalParams
         in pure $ sureLift [hs| get =<< $(maybeWrapThis texp) |]

tEffExp (ABS.ProTry pexp) _ = do
    scopeLevels <- get
    (locals,fields,hasForeigns) <- depends pexp
    let (formalParams, localVars) = (last scopeLevels, M.unions $ init scopeLevels)
        maybeWrapThis = if null fields then id else (\ e -> [hs| (\ this'' -> $e) =<< I'.readIORef this'|])
        maybeLift = if ?isInit then id else (\e -> [hs| I'.lift ($e)|])
    pure $ if null locals && not hasForeigns
           then let texp = runReader (let ?tyvars = [] in tPureExp pexp) formalParams
                in maybeLift $ maybeWrapThis [hs| pro_try $texp |]
           else let texp = runReader (let ?vars = localVars in tStmExp pexp) formalParams
                in maybeLift [hs| pro_try =<< $(maybeWrapThis texp) |]


tEffExp ABS.ProNew isAlone = pure $ let maybeLift = if ?isInit then id else (\e -> [hs| I'.lift ($e)|])
                                    in maybeLift [hs| pro_new |]


-- HELPERS
----------

addToScope typ var@(ABS.L (p,pid)) = do
  (topscope:restscopes) <- get
  if (any (\ scope -> var `M.member` scope) restscopes)
    then errorPos p $ pid ++ " already defined in an outer scope"
    else let newScopeLevels = M.insertWith (const $ const $ errorPos p $ pid ++ " already defined in this scope") var typ topscope  : restscopes
         in do
           put newScopeLevels
           return newScopeLevels


depends pexp = runReader (depends' pexp ([],[],False)) . M.unions . init <$> get
    where
 collectPatVars :: ABS.Pattern -> [ABS.L]
 collectPatVars (ABS.PVar ident) = [ident]
 collectPatVars (ABS.PParamConstr _ pats) = concatMap collectPatVars pats
 collectPatVars _ = []

 depends' pexp (rlocal,rfields,hasForeigns) = do
  scope <- ask
  case pexp of
    ABS.EThis ident -> pure (rlocal, ident:rfields,hasForeigns)
    ABS.EVar ident@(ABS.L (_,str)) -> pure $ if ident `M.member` scope 
                            then (ident:rlocal,rfields,hasForeigns)
                            else if ident `M.member` ?fields
                                 then (rlocal,ident:rfields,hasForeigns)
                                 else case find (\ (SN str' modul,_) -> str == str' && maybe False (not . snd) modul) (M.assocs ?st) of
                                        Just (_,SV Foreign _) ->  (rlocal, rfields,True)
                                        _ -> (rlocal, rfields,hasForeigns)
    ABS.ELet (ABS.FormalPar _ ident) pexpEq pexpIn -> do
                                    (rlocalEq, rfieldsEq,hasForeignsEq) <- depends' pexpEq ([],[],False)
                                    (rlocalIn, rfieldsIn,hasForeignsIn) <- let fields' = ?fields
                                                            in
                                                              let ?fields = M.delete ident fields' 
                                                              in local (M.delete ident) (depends' pexpIn ([],[],False))
                                    pure (rlocal++rlocalEq++rlocalIn, rfields++rfieldsEq++rfieldsIn,hasForeigns||hasForeignsEq||hasForeignsIn)
    -- ABS.ESinglConstr qtyp -> pure $ let (prefix, str) = splitQType qtyp
    --                                in case find (\ (SN str' modul,_) -> str == str' && maybe False (not . snd) modul) (M.assocs ?st) of
    --                                     Just (_,SV Foreign _) ->  (rlocal, rfields,True)
    --                                     _ -> (rlocal, rfields,hasForeigns)
    ABS.ECase pexpOf branches -> do
        (rlocalOf, rfieldsOf,hasForeignsOf) <- depends' pexpOf (rlocal,rfields,hasForeigns)      
        foldl (\ (acc1,acc2,acc3) (x1,x2,x3) -> (acc1++x1,acc2++x2,acc3||x3)) (rlocal++rlocalOf, rfields++rfieldsOf,hasForeigns||hasForeignsOf)
              <$> mapM (\ (ABS.ECaseBranch pat pexpBranch) ->
                  let fields' = ?fields
                      idents = collectPatVars pat
                  in
                    let ?fields = foldl (flip M.delete) fields' idents
                    in local (\ scope -> foldl (flip M.delete) scope idents) (depends' pexpBranch ([],[],False))
                  ) branches

    ABS.EOr e e' -> foldl (\ (acc1,acc2,acc3) (x1,x2,x3) -> (acc1++x1,acc2++x2,acc3||x3)) (rlocal, rfields, hasForeigns) <$> mapM (\ ex -> depends' ex ([],[],False)) [e,e']
    ABS.EAnd e e' -> foldl (\ (acc1,acc2,acc3) (x1,x2,x3) -> (acc1++x1,acc2++x2,acc3||x3)) (rlocal, rfields, hasForeigns) <$> mapM (\ ex -> depends' ex ([],[],False)) [e,e']
    ABS.EEq e e' -> foldl (\ (acc1,acc2,acc3) (x1,x2,x3) -> (acc1++x1,acc2++x2,acc3||x3)) (rlocal, rfields, hasForeigns) <$> mapM (\ ex -> depends' ex ([],[],False)) [e,e']
    ABS.ENeq e e' -> foldl (\ (acc1,acc2,acc3) (x1,x2,x3) -> (acc1++x1,acc2++x2,acc3||x3)) (rlocal, rfields, hasForeigns) <$> mapM (\ ex -> depends' ex ([],[],False)) [e,e']
    ABS.ELt e e' -> foldl (\ (acc1,acc2,acc3) (x1,x2,x3) -> (acc1++x1,acc2++x2,acc3||x3)) (rlocal, rfields, hasForeigns) <$> mapM (\ ex -> depends' ex ([],[],False)) [e,e']
    ABS.ELe e e' -> foldl (\ (acc1,acc2,acc3) (x1,x2,x3) -> (acc1++x1,acc2++x2,acc3||x3)) (rlocal, rfields, hasForeigns) <$> mapM (\ ex -> depends' ex ([],[],False)) [e,e']
    ABS.EGt e e' -> foldl (\ (acc1,acc2,acc3) (x1,x2,x3) -> (acc1++x1,acc2++x2,acc3||x3)) (rlocal, rfields, hasForeigns) <$> mapM (\ ex -> depends' ex ([],[],False)) [e,e']
    ABS.EGe e e' -> foldl (\ (acc1,acc2,acc3) (x1,x2,x3) -> (acc1++x1,acc2++x2,acc3||x3)) (rlocal, rfields, hasForeigns) <$> mapM (\ ex -> depends' ex ([],[],False)) [e,e']
    ABS.EAdd e e' -> foldl (\ (acc1,acc2,acc3) (x1,x2,x3) -> (acc1++x1,acc2++x2,acc3||x3)) (rlocal, rfields, hasForeigns) <$> mapM (\ ex -> depends' ex ([],[],False)) [e,e']
    ABS.ESub e e' -> foldl (\ (acc1,acc2,acc3) (x1,x2,x3) -> (acc1++x1,acc2++x2,acc3||x3)) (rlocal, rfields, hasForeigns) <$> mapM (\ ex -> depends' ex ([],[],False)) [e,e']
    ABS.EMul e e' -> foldl (\ (acc1,acc2,acc3) (x1,x2,x3) -> (acc1++x1,acc2++x2,acc3||x3)) (rlocal, rfields, hasForeigns) <$> mapM (\ ex -> depends' ex ([],[],False)) [e,e']
    ABS.EDiv e e' -> foldl (\ (acc1,acc2,acc3) (x1,x2,x3) -> (acc1++x1,acc2++x2,acc3||x3)) (rlocal, rfields, hasForeigns) <$> mapM (\ ex -> depends' ex ([],[],False)) [e,e']
    ABS.EMod e e' -> foldl (\ (acc1,acc2,acc3) (x1,x2,x3) -> (acc1++x1,acc2++x2,acc3||x3)) (rlocal, rfields, hasForeigns) <$> mapM (\ ex -> depends' ex ([],[],False)) [e,e']
    ABS.ELogNeg e -> depends' e (rlocal, rfields, hasForeigns)
    ABS.EIntNeg e -> depends' e (rlocal, rfields, hasForeigns)
    ABS.EFunCall (ABS.L_ (ABS.L (_,str))) es -> foldl (\ (acc1,acc2,acc3) (x1,x2,x3) -> (acc1++x1,acc2++x2,acc3||x3)) 
              (case find (\ (SN str' modul,_) -> str == str' && maybe False (not . snd) modul) (M.assocs ?st) of
                 Just (_,SV Foreign _) ->  (rlocal, rfields,True)
                 _ -> (rlocal, rfields,hasForeigns)) <$> mapM (\ ex -> depends' ex ([],[],False)) es
    --ABS.EQualFunCall _ _ es -> foldl (\ (acc1,acc2,acc3) (x1,x2,x3) -> (acc1++x1,acc2++x2,acc3||x3)) (rlocal, rfields, hasForeigns) <$> mapM (\ ex -> depends' ex ([],[],False)) es
    ABS.ENaryFunCall (ABS.L_ (ABS.L (_,str))) es -> foldl (\ (acc1,acc2,acc3) (x1,x2,x3) -> (acc1++x1,acc2++x2,acc3||x3)) 
              (case find (\ (SN str' modul,_) -> str == str' && maybe False (not . snd) modul) (M.assocs ?st) of
                 Just (_,SV Foreign _) ->  (rlocal, rfields,True)
                 _ -> (rlocal, rfields,hasForeigns)) <$> mapM (\ ex -> depends' ex ([],[],False)) es
    --ABS.ENaryQualFunCall _ _ es -> foldl (\ (acc1,acc2,acc3) (x1,x2,x3) -> (acc1++x1,acc2++x2,acc3||x3)) (rlocal, rfields, hasForeigns) <$> mapM (\ ex -> depends' ex ([],[],False) ) es
    ABS.EParamConstr qtyp es -> foldl (\ (acc1,acc2,acc3) (x1,x2,x3) -> (acc1++x1,acc2++x2,acc3||x3)) (rlocal, rfields,hasForeigns) <$> mapM (\ ex -> depends' ex ([],[],False)) es
    ABS.EIf e e' e'' -> foldl (\ (acc1,acc2,acc3) (x1,x2,x3) -> (acc1++x1,acc2++x2,acc3||x3)) (rlocal, rfields,hasForeigns) <$>  mapM (\ ex -> depends' ex ([],[],False)) [e,e',e'']
    _ -> return (rlocal, rfields, hasForeigns)


