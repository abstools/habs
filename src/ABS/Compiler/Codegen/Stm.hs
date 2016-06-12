{-# LANGUAGE CPP, ImplicitParams, QuasiQuotes, LambdaCase #-}
module ABS.Compiler.Codegen.Stm
    ( tMethod
    ) where

import ABS.Compiler.Utils
import ABS.Compiler.Codegen.Base
import ABS.Compiler.Firstpass.Base
import ABS.Compiler.Codegen.Exp (tPureExp)
import ABS.Compiler.Codegen.StmExp (tStmExp)
import ABS.Compiler.Codegen.Pat
import ABS.Compiler.Codegen.Typ
import qualified ABS.AST as ABS
import qualified Language.Haskell.Exts.Syntax as HS
import Language.Haskell.Exts.QQ (hs)

import Control.Monad.Trans.State.Strict (evalState, get, put, modify')
import Control.Monad.Trans.Reader (runReader, ask, local)
import qualified Data.Map as M
import Data.Foldable (foldlM)
import Data.List (nub, find)

import Control.Exception (assert)
#define todo assert False (error "not implemented yet")
#define total assert False (error "This error should not happen. Contact developers")

tMethod :: (?absFileName::String, ?st::SymbolTable) => [ABS.AnnStm] -> [ABS.FormalPar] -> ScopeLVL -> String -> [String] -> Bool -> HS.Exp
tMethod body formalParams fields cname cAloneMethods isInit = 
  evalState (let ?fields = fields  -- fixed fields passed as an implicit param
                 ?cname = cname    -- className needed for field pattern-matching
                 ?cAloneMethods = cAloneMethods
                 ?isInit = isInit
             in do
                  tstms <- concat <$> mapM tStm body
                  pure $ if null tstms
                         then [hs|I'.pure ()|] -- in Haskell empty stmt-body is not empty, but: pure ()
                         else HS.Do $ case last tstms of 
                                HS.Generator _ _ _ ->  tstms ++ [HS.Qualifier $ [hs|I'.pure ()|]] -- Haskell restriction
                                _ -> tstms)
  -- the state is a scope-stack
  [ M.empty -- level 2. new empty scope
  , M.fromList $ map (\ (ABS.FormalPar t i) -> (i,t)) formalParams  -- level 1. passed formal params
  ]

---------------- LOCAL VARIABLE ASSIGNMENT
tAss :: (?absFileName::String, ?cAloneMethods::[String], ?cname::String, ?fields::ScopeLVL, ?isInit::Bool, ?st::SymbolTable) 
     => [ABS.Ann]
     -> ABS.T
     -> ABS.L
     -> ABS.Exp
     -> BlockScope HS.Exp
tAss _ _ (ABS.L (_,n)) (ABS.ExpP pexp) = do
  (formalParams, localVars) <- getFormalLocal
  (_, fields,onlyPureDeps) <- depends [pexp]
  pure $ maybeLift $
    if onlyPureDeps
    then let texp = runReader (let ?tyvars = [] in tPureExp pexp) formalParams
         in maybeThis fields [hs|I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n) $texp|]
    else let texp = runReader (let ?vars = localVars in tStmExp pexp) formalParams
         in [hs|I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n) =<< $(maybeThis fields texp)|]

tAss _ (ABS.TSimple qu) (ABS.L (_,n)) (ABS.ExpE (ABS.New qcname args)) = do
  (formalParams, localVars) <- getFormalLocal
  (_,fields,onlyPureDeps) <- depends args
  let (q, cname) = splitQU qcname
      smartCon = HS.Var $ (if null q then HS.UnQual else HS.Qual $ HS.ModuleName q) $ HS.Ident $ "smart'" ++ cname
      initFun = HS.Var $ (if null q then HS.UnQual else HS.Qual $ HS.ModuleName q) $ HS.Ident $ "init'" ++ cname
  pure $ maybeLift $ 
    if onlyPureDeps
    then let smartApplied = runReader (let ?tyvars = [] in foldlM
                                                         (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                         smartCon
                                                         args) formalParams
         in maybeThis fields [hs|((I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n) . $(HS.Var $ HS.UnQual $ HS.Ident $ showQU qu)) =<< new $initFun $smartApplied)|]
    else let smartApplied = runReader (let ?vars = localVars in foldlM
                                               (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs|$acc <*> $targ|])
                                               [hs|I'.pure $smartCon|]
                                               args) formalParams
         in [hs|(I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n) . $(HS.Var $ HS.UnQual $ HS.Ident $ showQU qu)) =<< (new $initFun =<< $(maybeThis fields smartApplied))|]
tAss _ (ABS.TPoly _ _) (ABS.L (p,_)) (ABS.ExpE (ABS.New _ _)) = errorPos p "Interface cannot have polymorphic type"
tAss _ ABS.TInfer (ABS.L (p, _)) (ABS.ExpE (ABS.New _ _)) = errorPos p "Cannot infer interface-types"

tAss _ (ABS.TSimple qu) (ABS.L (_,n)) (ABS.ExpE (ABS.NewLocal qcname args)) = do
  (formalParams, localVars) <- getFormalLocal
  (_,fields,onlyPureDeps) <- depends args
  let (q, cname) = splitQU qcname
      smartCon = HS.Var $ (if null q then HS.UnQual else HS.Qual $ HS.ModuleName q) $ HS.Ident $ "smart'" ++ cname
      initFun = HS.Var $ (if null q then HS.UnQual else HS.Qual $ HS.ModuleName q) $ HS.Ident $ "init'" ++ cname
  pure $ maybeLift $
    if onlyPureDeps
    then let smartApplied = runReader (let ?tyvars = [] in foldlM
                                                         (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                         smartCon
                                                         args) formalParams
         in maybeThis fields [hs|((I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n) . $(HS.Var $ HS.UnQual $ HS.Ident $ showQU qu)) =<< newlocal' this $initFun $smartApplied)|]
    else let smartApplied = runReader (let ?vars = localVars in foldlM
                                               (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs|$acc <*> $targ|])
                                               [hs|I'.pure $smartCon|]
                                               args) formalParams
         in [hs|(I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n) . $(HS.Var $ HS.UnQual $ HS.Ident $ showQU qu)) =<< (newlocal' this $initFun =<< $(maybeThis fields smartApplied))|]
tAss _ (ABS.TPoly _ _) (ABS.L (p,_)) (ABS.ExpE (ABS.NewLocal _ _)) = errorPos p "Interface cannot have polymorphic type"
tAss _ ABS.TInfer (ABS.L (p, _)) (ABS.ExpE (ABS.NewLocal _ _)) = errorPos p "Cannot infer interface-types"

tAss a typ i@(ABS.L (_,n)) (ABS.ExpE (ABS.SyncMethCall pexp (ABS.L (p,mname)) args)) =
  case pexp of
   ABS.EVar ident@(ABS.L (_,calleeVar)) -> do
    (formalParams, localVars) <- getFormalLocal
    scopeLevels <- get
    case M.lookup ident (M.unions scopeLevels) of      -- check type in the scopes
      Just (ABS.TSimple qu) -> do -- only interface type
          (_,fields,onlyPureDeps) <- depends args
          let (prefix, iident) = splitQU qu
              iname = (if null prefix then HS.UnQual else HS.Qual $ HS.ModuleName prefix) $ HS.Ident iident
          pure $ maybeThisLifted fields $
            if onlyPureDeps
            then let mapplied = runReader (let ?tyvars = [] in foldlM
                                                              (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                              (HS.Var $ HS.UnQual $ HS.Ident mname)
                                                              args) formalParams
                     mwrapped = HS.Lambda (mkLoc p) [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs|sync' this obj' $mapplied|]
                 in if ident `M.member` formalParams
                    then [hs|(I'.lift . I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n)) =<< (($mwrapped) $(HS.Var $ HS.UnQual $ HS.Ident calleeVar))|]
                    else [hs|(I'.lift . I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n)) =<< (($mwrapped) =<< I'.lift (I'.readIORef $(HS.Var $ HS.UnQual $ HS.Ident calleeVar)))|]
            else let mapplied = runReader (let ?vars = localVars in foldlM
                                                         (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs|$acc <*> $targ|])
                                                         [hs|I'.pure $(HS.Var $ HS.UnQual $ HS.Ident mname)|]
                                                         args) formalParams
                     mwrapped = HS.Lambda (mkLoc p) [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs|sync' this obj' =<< I'.lift ($mapplied)|]
                 in if ident `M.member` formalParams
                    then [hs|(I'.lift . I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n)) =<< (($mwrapped) $(HS.Var $ HS.UnQual $ HS.Ident calleeVar))|]
                    else [hs|(I'.lift . I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n)) =<< (($mwrapped) =<< I'.lift (I'.readIORef $(HS.Var $ HS.UnQual $ HS.Ident calleeVar)))|]
      Just _ -> errorPos p "caller variable not of interface type"
      Nothing -> if ident `M.member` ?fields
                 then tAss a typ i (ABS.ExpE (ABS.SyncMethCall (ABS.EField ident) (ABS.L (p,mname)) args)) -- rewrite it to this.var
                 else errorPos p "cannot find variable"
   ABS.EField ident ->
     case M.lookup ident ?fields of
      Just (ABS.TSimple qu) -> do -- only interface type
          (formalParams, localVars) <- getFormalLocal
          (_,_,onlyPureDeps) <- depends args
          let (prefix, iident) = splitQU qu
              iname = (if null prefix then HS.UnQual else HS.Qual $ HS.ModuleName prefix) $ HS.Ident iident
          pure $
            if onlyPureDeps
            then let mapplied = runReader (let ?tyvars = [] in foldlM
                                                         (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                         (HS.Var $ HS.UnQual $ HS.Ident mname) args) formalParams

                     mwrapped = HS.Lambda (mkLoc p) [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs|sync' this obj' $mapplied|]
                 in [hs|(\ this'' -> (I'.lift . I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n)) =<< ($mwrapped ($(fieldFun ident) this''))) =<< I'.lift (I'.readIORef this')|]
            else let mapplied = runReader (let ?vars = localVars in foldlM
                                                    (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs|$acc <*> $targ|])
                                                    [hs|I'.pure $(HS.Var $ HS.UnQual $ HS.Ident mname)|]                                                    
                                                    args) formalParams
                     mwrapped = HS.Lambda (mkLoc p) [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs|sync' this obj' =<< I'.lift ($mapplied)|]
                  in [hs|(\ this'' -> (I'.lift . I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n)) =<< ($mwrapped ($(fieldFun ident) this''))) =<< I'.lift (I'.readIORef this')|]
      Just _ -> errorPos p "caller field not of interface type"
      Nothing -> errorPos p "no such field"
   ABS.ELit ABS.LNull -> errorPos p "null cannot be the object callee"
   _ -> errorPos p "current compiler limitation: the object callee cannot be an arbitrary pure-exp"

tAss _ _ (ABS.L (_,n)) (ABS.ExpE (ABS.ThisSyncMethCall (ABS.L (_,mname)) args)) = do
  (formalParams, localVars) <- getFormalLocal
  (_,fields,onlyPureDeps) <- depends args
  pure $
    if onlyPureDeps
    then let mapplied = runReader (let ?tyvars = [] in foldlM
                                                      (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                      (maybeMangleCall mname)
                                                      args) formalParams
             ioAction = [hs|(this <..> $mapplied)|]
         in [hs|(I'.lift . I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n)) =<< $(maybeThisLifted fields ioAction)|]
    else let mapplied = runReader (let ?vars = localVars in foldlM
                                                 (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs|$acc <*> $targ|])
                                                 ((\ e-> [hs|I'.pure $e|]) (maybeMangleCall mname))
                                                 args) formalParams
         in [hs|(I'.lift . I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n)) =<< ((this <..>) =<< I'.lift $(maybeThis fields mapplied))|]

tAss a typ i@(ABS.L (_,n)) (ABS.ExpE (ABS.AsyncMethCall pexp (ABS.L (p,mname)) args)) =
 case pexp of
  ABS.ELit ABS.LThis -> do
    (formalParams, localVars) <- getFormalLocal
    (_,fields,onlyPureDeps) <- depends args
    pure $ maybeLift $
      if onlyPureDeps
      then let mapplied = runReader (let ?tyvars = [] in foldlM
                                                 (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                 (maybeMangleCall mname)
                                                 args) formalParams
           in maybeThis fields [hs|(I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n) =<< (this <!> $mapplied))|]
      else let mapplied = runReader (let ?vars = localVars in foldlM
                                                                        (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs|$acc <*> $targ|])
                                                                        ((\ e-> [hs|I'.pure $e|]) (maybeMangleCall mname))
                                                                        args) formalParams
           in [hs|I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n) =<< ((this <!>) =<< $(maybeThis fields mapplied))|]
  ABS.EVar ident@(ABS.L (_, calleeVar)) -> do
    (formalParams, localVars) <- getFormalLocal
    scopeLevels <- get
    case M.lookup ident $ M.unions scopeLevels of -- check type in the scopes
      Just (ABS.TSimple qu) -> do -- only interface type
          (_,fields,onlyPureDeps) <- depends args
          let (prefix, iident) = splitQU qu
              iname = (if null prefix then HS.UnQual else HS.Qual $ HS.ModuleName prefix) $ HS.Ident iident
          pure $ maybeLift $
            if onlyPureDeps
            then let mapplied = runReader (let ?tyvars = [] in foldlM
                                                         (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                         (HS.Var $ HS.UnQual $ HS.Ident mname) args) formalParams
                     mwrapped = HS.Lambda (mkLoc p) [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs|(obj' <!> $mapplied)|]
                 in maybeThis fields $ 
                   if ident `M.member` formalParams
                   then [hs|I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n) =<< (($mwrapped) $(HS.Var $ HS.UnQual $ HS.Ident calleeVar))|]
                   else [hs|I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n) =<< (($mwrapped) =<< I'.readIORef $(HS.Var $ HS.UnQual $ HS.Ident calleeVar))|]
            else let mapplied = runReader (let ?vars = localVars in foldlM
                                                                            (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs|$acc <*> $targ|])
                                                                            [hs|I'.pure $(HS.Var $ HS.UnQual $ HS.Ident mname)|]
                                                                            args) formalParams
                     mwrapped = HS.Lambda (mkLoc p) [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs|(obj' <!>) =<< $mapplied|]
                 in if ident `M.member` formalParams
                    then [hs|I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n) =<< (($(maybeThis fields mwrapped)) $(HS.Var $ HS.UnQual $ HS.Ident calleeVar))|] 
                    else [hs|I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n) =<< (($(maybeThis fields mwrapped)) =<< I'.readIORef $(HS.Var $ HS.UnQual $ HS.Ident calleeVar))|]
      Nothing -> if ident `M.member` ?fields
                 then tAss a typ i (ABS.ExpE (ABS.AsyncMethCall (ABS.EField ident) (ABS.L (p,mname)) args)) -- rewrite it to this.var
                 else errorPos p "cannot find variable"
      _ -> errorPos p "invalid object callee type"
  ABS.EField ident ->
    case M.lookup ident ?fields of
      Just (ABS.TSimple qu) -> do -- only interface type
          (formalParams, localVars) <- getFormalLocal
          (_,_,onlyPureDeps) <- depends args
          let (prefix, iident) = splitQU qu
              iname = (if null prefix then HS.UnQual else HS.Qual $ HS.ModuleName prefix) $ HS.Ident iident
          pure $ maybeLift $ 
            if onlyPureDeps
            then let mapplied = runReader (let ?tyvars = [] in foldlM
                                                         (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                         (HS.Var $ HS.UnQual $ HS.Ident mname) args) formalParams
                     mwrapped = HS.Lambda (mkLoc p) [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs|(obj' <!> $mapplied)|]
                 in [hs|(\ this'' -> I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n) =<< ($mwrapped ($(fieldFun ident) this''))) =<< I'.readIORef this'|]
            else let mapplied = runReader (let ?vars = localVars in foldlM
                                                    (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs|$acc <*> $targ|])
                                                    [hs|I'.pure $(HS.Var $ HS.UnQual $ HS.Ident mname)|]                                                    
                                                    args) formalParams
                     mwrapped = HS.Lambda (mkLoc p) [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs|(obj' <!>) =<< $mapplied|]
                 in [hs|(\ this'' -> I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n) =<< ($mwrapped ($(fieldFun ident) this''))) =<< I'.readIORef this'|]
      Just _ -> errorPos p "caller field not of interface type"
      Nothing -> errorPos p "no such field"
  ABS.ELit ABS.LNull -> errorPos p "null cannot be the object callee"
  _ -> errorPos p "current compiler limitation: the object callee cannot be an arbitrary pure-exp"

tAss a typ i@(ABS.L (_,n)) (ABS.ExpE (ABS.AwaitMethCall pexp (ABS.L (p,mname)) args)) =
 case pexp of
  ABS.ELit ABS.LThis -> do
    (formalParams, localVars) <- getFormalLocal
    (_,fields,onlyPureDeps) <- depends args
    pure $
      if onlyPureDeps 
      then let mapplied = runReader (let ?tyvars = [] in foldlM
                                                         (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                         (maybeMangleCall mname)
                                                         args) formalParams
           in maybeThisLifted fields [hs|awaitSugar' this (I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n)) this ($mapplied)|]
      else let mapplied = runReader (let ?vars = localVars in foldlM
                                                    (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs|$acc <*> $targ|])
                                                    ((\ e-> [hs|I'.pure $e|]) (maybeMangleCall mname))
                                                    args) formalParams
           in [hs|awaitSugar' this (I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n)) this =<< I'.lift $(maybeThis fields mapplied)|]
  ABS.EVar ident@(ABS.L (_, calleeVar)) -> do
    (formalParams, localVars) <- getFormalLocal
    scopeLevels <- get
    case M.lookup ident $ M.unions scopeLevels of -- check type in the scopes
      Just (ABS.TSimple qu) -> do -- only interface type
          (_,fields,onlyPureDeps) <- depends args
          let (prefix, iident) = splitQU qu
              iname = (if null prefix then HS.UnQual else HS.Qual $ HS.ModuleName prefix) $ HS.Ident iident
          pure $
            if onlyPureDeps
            then let mapplied = runReader (let ?tyvars = [] in foldlM
                                                         (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                         (HS.Var $ HS.UnQual $ HS.Ident mname) args) formalParams
                     mwrapped = HS.Lambda (mkLoc p) [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs|awaitSugar' this (I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n)) obj' ($mapplied)|]
                 in if ident `M.member` formalParams
                    then [hs|($(maybeThisLifted fields mwrapped)) $(HS.Var $ HS.UnQual $ HS.Ident calleeVar)|]
                    else [hs|($(maybeThisLifted fields mwrapped)) =<< I'.lift (I'.readIORef $(HS.Var $ HS.UnQual $ HS.Ident calleeVar))|]
            else let mapplied = runReader (let ?vars = localVars in foldlM
                                                                            (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs|$acc <*> $targ|])
                                                                            [hs|I'.pure $(HS.Var $ HS.UnQual $ HS.Ident mname)|]
                                                                            args) formalParams
                     mwrapped = HS.Lambda (mkLoc p) [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs|awaitSugar' this (I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n)) obj'  =<<  I'.lift ($mapplied)|]
                 in if ident `M.member` formalParams
                    then [hs|($(maybeThisLifted fields mwrapped)) $(HS.Var $ HS.UnQual $ HS.Ident calleeVar)|] 
                    else [hs|($(maybeThisLifted fields mwrapped)) =<< I'.lift (I'.readIORef $(HS.Var $ HS.UnQual $ HS.Ident calleeVar))|]
      Nothing -> if ident `M.member` ?fields
                 then tAss a typ i (ABS.ExpE (ABS.AwaitMethCall (ABS.EField ident) (ABS.L (p,mname)) args)) -- rewrite it to this.var
                 else errorPos p "cannot find variable"
      _ -> errorPos p "invalid object callee type"
  ABS.EField ident ->
    case M.lookup ident ?fields of
      Just (ABS.TSimple qu) -> do -- only interface type
          (formalParams, localVars) <- getFormalLocal
          (_,_,onlyPureDeps) <- depends args
          let (prefix, iident) = splitQU qu
              iname = (if null prefix then HS.UnQual else HS.Qual $ HS.ModuleName prefix) $ HS.Ident iident
          pure $ 
            if onlyPureDeps
            then let mapplied = runReader (let ?tyvars = [] in foldlM
                                                         (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                         (HS.Var $ HS.UnQual $ HS.Ident mname) args) formalParams
                     mwrapped = HS.Lambda (mkLoc p) [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs|awaitSugar' this (I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n)) obj' ($mapplied)|]
                 in [hs|(\ this'' -> ($mwrapped) ($(fieldFun ident) this'')) =<< I'.lift (I'.readIORef this')|]
            else let mapplied = runReader (let ?vars = localVars in foldlM
                                                    (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs|$acc <*> $targ|])
                                                    [hs|I'.pure $(HS.Var $ HS.UnQual $ HS.Ident mname)|]
                                                    args) formalParams
                     mwrapped = HS.Lambda (mkLoc p) [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs|awaitSugar' this (I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n)) obj'  =<<  I'.lift ($mapplied)|]
                 in [hs|(\ this'' -> ($mwrapped) ($(fieldFun ident) this'')) =<< I'.lift (I'.readIORef this')|]
      Just _ -> errorPos p "caller field not of interface type"
      Nothing -> errorPos p "no such field"
  ABS.ELit ABS.LNull -> errorPos p "null cannot be the object callee"
  _ -> errorPos p "current compiler limitation: the object callee cannot be an arbitrary pure-exp"


tAss _ _ (ABS.L (_,n)) (ABS.ExpE (ABS.Get pexp)) = do
  (formalParams, localVars) <- getFormalLocal
  (_,fields,onlyPureDeps) <- depends [pexp]
  let sureLift = if ?isInit then error "get not allowed inside init" else (\e -> [hs|I'.lift ($e)|])
  pure $ sureLift $
    if onlyPureDeps
    then let texp = runReader (let ?tyvars = [] in tPureExp pexp) formalParams
         in maybeThis fields [hs|I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n) =<< get $texp|]
    else let texp = runReader (let ?vars = localVars in tStmExp pexp) formalParams
         in [hs|I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n) =<< (get =<< $(maybeThis fields texp))|]

tAss _ _ (ABS.L (_,n)) (ABS.ExpE (ABS.ProTry pexp)) = do
  (formalParams, localVars) <- getFormalLocal
  (_,fields,onlyPureDeps) <- depends [pexp]
  pure $ maybeLift $
    if onlyPureDeps
    then let texp = runReader (let ?tyvars = [] in tPureExp pexp) formalParams
         in maybeThis fields [hs|I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n) =<< pro_try $texp|]
    else let texp = runReader (let ?vars = localVars in tStmExp pexp) formalParams
         in [hs|I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n) =<< (pro_try =<< $(maybeThis fields texp))|]

tAss _ _ (ABS.L (_,n)) (ABS.ExpE ABS.ProNew) = pure $ maybeLift [hs|I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n) =<< pro_new|]
tAss _ _ (ABS.L (_,n)) (ABS.ExpE ABS.Now) = pure $ maybeLift [hs|I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n) =<< now|]
tAss _ _ (ABS.L (_,n)) (ABS.ExpE ABS.Readln) = pure $ maybeLift [hs|I'.writeIORef $(HS.Var $ HS.UnQual $ HS.Ident n) =<< readln|]


------------- DECLARATION+LOCAL VARIABLE ASSIGNMENT

tDecAss :: (?absFileName::String, ?cAloneMethods::[String], ?cname::String, ?fields::ScopeLVL, ?isInit::Bool, ?st::SymbolTable) 
     => [ABS.Ann]
     -> ABS.T
     -> ABS.L
     -> ABS.Exp
     -> BlockScope HS.Exp
tDecAss _ _ _ (ABS.ExpE (ABS.AwaitMethCall _ _ _)) = total
tDecAss _ _ _ (ABS.ExpP pexp) = do
  (formalParams, localVars) <- getFormalLocal
  (_, fields,onlyPureDeps) <- depends [pexp]
  pure $ maybeLift $
    if onlyPureDeps
    then let texp = runReader (let ?tyvars = [] in tPureExp pexp) formalParams
         in maybeThis fields [hs|I'.newIORef $texp|]
    else let texp = runReader (let ?vars = localVars in tStmExp pexp) formalParams
         in [hs|I'.newIORef =<< $(maybeThis fields texp)|]


tDecAss _ (ABS.TSimple qu) _ (ABS.ExpE (ABS.New qcname args)) = do
  (formalParams, localVars) <- getFormalLocal
  (_,fields,onlyPureDeps) <- depends args
  let (q, cname) = splitQU qcname
      smartCon = HS.Var $ (if null q then HS.UnQual else HS.Qual $ HS.ModuleName q) $ HS.Ident $ "smart'" ++ cname
      initFun = HS.Var $ (if null q then HS.UnQual else HS.Qual $ HS.ModuleName q) $ HS.Ident $ "init'" ++ cname
  pure $ maybeLift $
    if onlyPureDeps
    then let smartApplied = runReader (let ?tyvars = [] in foldlM
                                           (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                           smartCon
                                           args) formalParams
         in maybeThis fields [hs|((I'.newIORef . $(HS.Var $ HS.UnQual $ HS.Ident $ showQU qu)) =<< new $initFun $smartApplied)|]
    else let smartApplied = runReader (let ?vars = localVars in foldlM
                                               (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs|$acc <*> $targ|])
                                               [hs|I'.pure $smartCon|]
                                               args) formalParams
         in [hs|(I'.newIORef . $(HS.Var $ HS.UnQual $ HS.Ident $ showQU qu)) =<< (new $initFun =<< $(maybeThis fields smartApplied))|]
tDecAss _ (ABS.TPoly _ _) (ABS.L (p,_)) (ABS.ExpE (ABS.New _ _)) = errorPos p "Interface cannot have polymorphic type"
tDecAss _ ABS.TInfer (ABS.L (p, _)) (ABS.ExpE (ABS.New _ _)) = errorPos p "Cannot infer interface-types"

tDecAss _ (ABS.TSimple qu) _ (ABS.ExpE (ABS.NewLocal qcname args)) = do
  (formalParams, localVars) <- getFormalLocal
  (_,fields,onlyPureDeps) <- depends args
  let (q, cname) = splitQU qcname
      smartCon = HS.Var $ (if null q then HS.UnQual else HS.Qual $ HS.ModuleName q) $ HS.Ident $ "smart'" ++ cname
      initFun = HS.Var $ (if null q then HS.UnQual else HS.Qual $ HS.ModuleName q) $ HS.Ident $ "init'" ++ cname
  pure $ maybeLift $
    if onlyPureDeps
    then let smartApplied = runReader (let ?tyvars = [] in foldlM
                                           (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                           smartCon
                                           args) formalParams
         in maybeThis fields [hs|((I'.newIORef . $(HS.Var $ HS.UnQual $ HS.Ident $ showQU qu)) =<< newlocal' this $initFun $smartApplied)|]
    else let smartApplied = runReader (let ?vars = localVars in foldlM
                                               (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs|$acc <*> $targ|])
                                               [hs|I'.pure $smartCon|]
                                               args) formalParams
         in [hs|(I'.newIORef . $(HS.Var $ HS.UnQual $ HS.Ident $ showQU qu)) =<< (newlocal' this $initFun =<< $(maybeThis fields smartApplied))|]
tDecAss _ (ABS.TPoly _ _) (ABS.L (p,_)) (ABS.ExpE (ABS.NewLocal _ _)) = errorPos p "Interface cannot have polymorphic type"
tDecAss _ ABS.TInfer (ABS.L (p, _)) (ABS.ExpE (ABS.NewLocal _ _)) = errorPos p "Cannot infer interface-types"

tDecAss a t i (ABS.ExpE (ABS.SyncMethCall pexp (ABS.L (p,mname)) args)) =
  case pexp of
   ABS.EVar ident@(ABS.L (_, calleeVar)) -> do
    typ <- M.lookup ident . M.unions <$> get -- check type in the scopes
    case typ of
      Just (ABS.TSimple qtyp) -> do -- only interface type
          (formalParams, localVars) <- getFormalLocal
          (_,fields,onlyPureDeps) <- depends args
          let (prefix, iident) = splitQU qtyp
              iname = (if null prefix then HS.UnQual else HS.Qual $ HS.ModuleName prefix) $ HS.Ident iident
          pure $ maybeThisLifted fields $
            if onlyPureDeps
            then let mapplied = runReader (let ?tyvars = [] in foldlM
                                                              (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                              (HS.Var $ HS.UnQual $ HS.Ident mname)
                                                              args) formalParams
                     mwrapped = HS.Lambda noLoc' [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs|sync' this obj' $mapplied|]
                 in if ident `M.member` formalParams
                    then [hs|(I'.lift . I'.newIORef) =<< (($mwrapped) $(HS.Var $ HS.UnQual $ HS.Ident calleeVar))|]
                    else [hs|(I'.lift . I'.newIORef) =<< (($mwrapped) =<< I'.lift (I'.readIORef $(HS.Var $ HS.UnQual $ HS.Ident calleeVar)))|]
             else let mapplied = runReader (let ?vars = localVars in foldlM
                                                         (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs|$acc <*> $targ|])
                                                         [hs|I'.pure $(HS.Var $ HS.UnQual $ HS.Ident mname)|]
                                                         args) formalParams
                      mwrapped = HS.Lambda noLoc' [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs|sync' this obj' =<< I'.lift ($mapplied)|]
                  in if ident `M.member` formalParams
                     then [hs|(I'.lift . I'.newIORef) =<< (($mwrapped) $(HS.Var $ HS.UnQual $ HS.Ident calleeVar))|]
                     else [hs|(I'.lift . I'.newIORef) =<< (($mwrapped) =<< I'.lift (I'.readIORef $(HS.Var $ HS.UnQual $ HS.Ident calleeVar)))|]
      Just _ -> errorPos p "caller variable not of interface type"
      Nothing -> if ident `M.member` ?fields
                 then tDecAss a t i (ABS.ExpE (ABS.SyncMethCall (ABS.EField ident) (ABS.L (p,mname)) args))-- rewrite it to this.var
                 else errorPos p "cannot find variable"
   ABS.EField ident ->
     case M.lookup ident ?fields of
      Just (ABS.TSimple qu) -> do -- only interface type
          (formalParams, localVars) <- getFormalLocal
          (_,_,onlyPureDeps) <- depends args
          let (prefix, iident) = splitQU qu
              iname = (if null prefix then HS.UnQual else HS.Qual $ HS.ModuleName prefix) $ HS.Ident iident
          pure $ if onlyPureDeps
                 then let mapplied = runReader (let ?tyvars = [] in foldlM
                                                         (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                         (HS.Var $ HS.UnQual $ HS.Ident mname) args) formalParams

                          mwrapped = HS.Lambda noLoc' [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs|sync' this obj' $mapplied|]
                 in [hs|(\ this'' -> (I'.lift . I'.newIORef) =<< ($mwrapped ($(fieldFun ident) this''))) =<< I'.lift (I'.readIORef this')|]
            else let mapplied = runReader (let ?vars = localVars in foldlM
                                                    (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs|$acc <*> $targ|])
                                                    [hs|I'.pure $(HS.Var $ HS.UnQual $ HS.Ident mname)|]                                                    
                                                    args) formalParams
                     mwrapped = HS.Lambda noLoc' [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs|sync' this obj' =<< I'.lift ($mapplied)|]
                  in [hs|(\ this'' -> (I'.lift . I'.newIORef) =<< ($mwrapped ($(fieldFun ident) this''))) =<< I'.lift (I'.readIORef this')|]
      Just _ -> errorPos p "caller field not of interface type"
      Nothing -> errorPos p "no such field"
   ABS.ELit ABS.LNull -> errorPos p "null cannot be the object callee"
   _ -> errorPos p "current compiler limitation: the object callee cannot be an arbitrary pure-exp"

tDecAss _ _ _ (ABS.ExpE (ABS.ThisSyncMethCall (ABS.L (_,mname)) args)) = do
  (formalParams, localVars) <- getFormalLocal
  (_,fields,onlyPureDeps) <- depends args
  pure $
    if onlyPureDeps
    then let mapplied = runReader (let ?tyvars = [] in foldlM
                                                      (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                      (maybeMangleCall mname)
                                                      args) formalParams
             ioAction = [hs|(this <..> $mapplied)|]
         in [hs|(I'.lift . I'.newIORef) =<< $(maybeThisLifted fields ioAction)|]
    else let mapplied = runReader (let ?vars = localVars in foldlM
                                                 (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs|$acc <*> $targ|])
                                                 ((\ e-> [hs|I'.pure $e|]) (maybeMangleCall mname))
                                                 args) formalParams
         in [hs|(I'.lift . I'.newIORef) =<< ((this <..>) =<< I'.lift $(maybeThis fields mapplied))|]

tDecAss a t i (ABS.ExpE (ABS.AsyncMethCall pexp (ABS.L (p,mname)) args)) =
 case pexp of
  ABS.ELit ABS.LThis -> do
    (formalParams, localVars) <- getFormalLocal
    (_,fields,onlyPureDeps) <- depends args
    pure $ maybeLift $
      if onlyPureDeps
      then let mapplied = runReader (let ?tyvars = [] in foldlM
                                                 (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                 (maybeMangleCall mname)
                                                 args) formalParams
           in maybeThis fields [hs|(I'.newIORef =<< (this <!> $mapplied))|]
      else let mapplied = runReader (let ?vars = localVars in foldlM
                                                                        (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs|$acc <*> $targ|])
                                                                        ((\ e-> [hs|I'.pure $e|]) (maybeMangleCall mname))
                                                                        args) formalParams
           in [hs|I'.newIORef =<< ((this <!>) =<< $(maybeThis fields mapplied))|]
  ABS.EVar ident@(ABS.L (_,calleeVar)) -> do
    typ <- M.lookup ident . M.unions <$> get -- check type in the scopes
    case typ of
      Just (ABS.TSimple qu) -> do -- only interface type
          (formalParams, localVars) <- getFormalLocal
          (_,fields,onlyPureDeps) <- depends args
          let (prefix, iident) = splitQU qu
              iname = (if null prefix then HS.UnQual else HS.Qual $ HS.ModuleName prefix) $ HS.Ident iident
          pure $ maybeLift $
            if onlyPureDeps
            then let mapplied = runReader (let ?tyvars = [] in foldlM
                                                         (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                         (HS.Var $ HS.UnQual $ HS.Ident mname) args) formalParams
                     mwrapped = HS.Lambda noLoc' [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs|(obj' <!> $mapplied)|]
                 in maybeThis fields $ if ident `M.member` formalParams
                                    then [hs|I'.newIORef =<< (($mwrapped) $(HS.Var $ HS.UnQual $ HS.Ident calleeVar))|]
                                    else [hs|I'.newIORef =<< (($mwrapped) =<< I'.readIORef $(HS.Var $ HS.UnQual $ HS.Ident calleeVar))|]
            else let mapplied = runReader (let ?vars = localVars in foldlM 
                                                                            (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs|$acc <*> $targ|])
                                                                            [hs|I'.pure $(HS.Var $ HS.UnQual $ HS.Ident mname)|]
                                                                            args) formalParams
                     mwrapped = HS.Lambda noLoc' [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs|(obj' <!>) =<< $mapplied|]
                 in if ident `M.member` formalParams
                    then [hs|I'.newIORef =<< (($(maybeThis fields mwrapped)) $(HS.Var $ HS.UnQual $ HS.Ident calleeVar))|]
                    else [hs|I'.newIORef =<< (($(maybeThis fields mwrapped)) =<< I'.readIORef $(HS.Var $ HS.UnQual $ HS.Ident calleeVar))|]
      Nothing -> if ident `M.member` ?fields
                 then tDecAss a t i (ABS.ExpE (ABS.AsyncMethCall (ABS.EField ident) (ABS.L (p,mname)) args)) -- rewrite it to this.var
                 else errorPos p "cannot find variable"
      _ -> errorPos p "invalid object callee type"
  ABS.EField ident ->
    case M.lookup ident ?fields of
      Just (ABS.TSimple qu) -> do -- only interface type
          (formalParams, localVars) <- getFormalLocal
          (_,_,onlyPureDeps) <- depends args
          let (prefix, iident) = splitQU qu
              iname = (if null prefix then HS.UnQual else HS.Qual $ HS.ModuleName prefix) $ HS.Ident iident
          pure $ maybeLift $
            if onlyPureDeps
            then let mapplied = runReader (let ?tyvars = [] in foldlM
                                                         (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                         (HS.Var $ HS.UnQual $ HS.Ident mname) args) formalParams
                     mwrapped = HS.Lambda noLoc' [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs|(obj' <!> $mapplied)|]
                 in [hs|(\ this'' -> I'.newIORef =<< ($mwrapped ($(fieldFun ident) this''))) =<< I'.readIORef this'|]
            else let mapplied = runReader (let ?vars = localVars in foldlM
                                                    (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs|$acc <*> $targ|])
                                                    [hs|I'.pure $(HS.Var $ HS.UnQual $ HS.Ident mname)|]                                                    
                                                    args) formalParams
                     mwrapped = HS.Lambda noLoc' [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs|(obj' <!>) =<< $mapplied|]
                 in [hs|(\ this'' -> I'.newIORef =<< ($mwrapped ($(fieldFun ident) this''))) =<< I'.readIORef this'|]
      Just _ -> errorPos p "caller field not of interface type"
      Nothing -> errorPos p "no such field"
  ABS.ELit ABS.LNull -> errorPos p "null cannot be the object callee"
  _ -> errorPos p "current compiler limitation: the object callee cannot be an arbitrary pure-exp"


tDecAss _ _ _ (ABS.ExpE (ABS.Get pexp)) = do
  (formalParams, localVars) <- getFormalLocal
  (_,fields,onlyPureDeps) <- depends [pexp]
  let sureLift = if ?isInit then error "get not allowed inside init" else (\e -> [hs|I'.lift ($e)|])
  pure $ sureLift $ 
    if onlyPureDeps
    then let texp = runReader (let ?tyvars = [] in tPureExp pexp) formalParams
         in maybeThis fields [hs|I'.newIORef =<< get $texp|]
    else let texp = runReader (let ?vars = localVars in tStmExp pexp) formalParams
         in [hs|I'.newIORef =<< (get =<< $(maybeThis fields texp))|]


tDecAss _ _ _ (ABS.ExpE (ABS.ProTry pexp)) = do
  (formalParams, localVars) <- getFormalLocal
  (_,fields,onlyPureDeps) <- depends [pexp]
  pure $ maybeLift $
    if onlyPureDeps
    then let texp = runReader (let ?tyvars = [] in tPureExp pexp) formalParams
         in maybeThis fields [hs|I'.newIORef =<< pro_try $texp|]
    else let texp = runReader (let ?vars = localVars in tStmExp pexp) formalParams
         in [hs|I'.newIORef =<< (pro_try =<< $(maybeThis fields texp))|]

tDecAss _ _ _ (ABS.ExpE ABS.ProNew) = pure $ maybeLift [hs|I'.newIORef =<< pro_new|]

tDecAss _ _ _ (ABS.ExpE ABS.Now) = pure $ maybeLift [hs|I'.newIORef =<< now|]

tDecAss _ _ _ (ABS.ExpE ABS.Readln) = pure $ maybeLift [hs|I'.newIORef =<< readln|]


------------------- FIELD ASSIGNMENT

tFieldAss a (ABS.L (_, field)) (ABS.ExpE (ABS.AwaitMethCall pexp (ABS.L (p,mname)) args)) = 
 case pexp of
  ABS.ELit ABS.LThis -> do
    (formalParams, localVars) <- getFormalLocal
    (_,_,onlyPureDeps) <- depends args
    pure $
      if onlyPureDeps 
      then let mapplied = runReader (let ?tyvars = [] in foldlM
                                                         (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                         (maybeMangleCall mname)
                                                         args) formalParams
           in [hs|(\ this'' -> awaitSugar' this (\ v'-> I'.writeIORef this' $(recordUpdate field)) this ($mapplied)) =<< I'.lift (I'.readIORef this')|]
      else let mapplied = runReader (let ?vars = localVars in foldlM
                                                    (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs|$acc <*> $targ|])
                                                    ((\ e-> [hs|I'.pure $e|]) (maybeMangleCall mname))
                                                    args) formalParams
           in [hs|(\ this'' -> awaitSugar' this (\ v'-> I'.writeIORef this' $(recordUpdate field)) this =<< I'.lift ($mapplied)) =<< I'.lift (I'.readIORef this')|]
  ABS.EVar ident@(ABS.L (_, calleeVar)) -> do
    (formalParams, localVars) <- getFormalLocal
    scopeLevels <- get
    case M.lookup ident $ M.unions scopeLevels of -- check type in the scopes
      Just (ABS.TSimple qu) -> do -- only interface type
          (_,_,onlyPureDeps) <- depends args
          let (prefix, iident) = splitQU qu
              iname = (if null prefix then HS.UnQual else HS.Qual $ HS.ModuleName prefix) $ HS.Ident iident
          pure $
            if onlyPureDeps
            then let mapplied = runReader (let ?tyvars = [] in foldlM
                                                         (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                         (HS.Var $ HS.UnQual $ HS.Ident mname) args) formalParams
                     mwrapped = HS.Lambda (mkLoc p) [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs|awaitSugar' this (\ v'-> I'.writeIORef this' $(recordUpdate field)) obj' ($mapplied)|]
                 in if ident `M.member` formalParams
                    then [hs|(\ this'' -> ($mwrapped) $(HS.Var $ HS.UnQual $ HS.Ident calleeVar)) =<< I'.lift (I'.readIORef this')|]
                    else [hs|(\ this'' -> ($mwrapped) =<< I'.lift (I'.readIORef $(HS.Var $ HS.UnQual $ HS.Ident calleeVar))) =<< I'.lift (I'.readIORef this')|]
            else let mapplied = runReader (let ?vars = localVars in foldlM
                                                                            (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs|$acc <*> $targ|])
                                                                            [hs|I'.pure $(HS.Var $ HS.UnQual $ HS.Ident mname)|]
                                                                            args) formalParams
                     mwrapped = HS.Lambda (mkLoc p) [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs|awaitSugar' this (\ v'-> I'.writeIORef this' $(recordUpdate field)) obj' =<< I'.lift ($mapplied)|]
                 in if ident `M.member` formalParams
                    then [hs|(\ this'' -> ($mwrapped) $(HS.Var $ HS.UnQual $ HS.Ident calleeVar)) =<< I'.lift (I'.readIORef this')|] 
                    else [hs|(\ this'' -> ($mwrapped) =<< I'.lift (I'.readIORef $(HS.Var $ HS.UnQual $ HS.Ident calleeVar))) =<< I'.lift (I'.readIORef this')|]
      Nothing -> if ident `M.member` ?fields
                 then tFieldAss a (ABS.L (p,field)) $ ABS.ExpE $ ABS.AwaitMethCall (ABS.EField ident) (ABS.L (p,mname)) args -- rewrite it to this.var
                 else errorPos p "cannot find variable"
      _ -> errorPos p "invalid object callee type"
  ABS.EField ident ->
    case M.lookup ident ?fields of
      Just (ABS.TSimple qu) -> do -- only interface type
          (formalParams, localVars) <- getFormalLocal
          (_,_,onlyPureDeps) <- depends args
          let (prefix, iident) = splitQU qu
              iname = (if null prefix then HS.UnQual else HS.Qual $ HS.ModuleName prefix) $ HS.Ident iident
          pure $
            if onlyPureDeps
            then let mapplied = runReader (let ?tyvars = [] in foldlM
                                                         (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                         (HS.Var $ HS.UnQual $ HS.Ident mname) args) formalParams
                     mwrapped = HS.Lambda (mkLoc p) [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs|awaitSugar' this (\ v'-> I'.writeIORef this' $(recordUpdate field)) obj' ($mapplied)|]
                 in [hs|(\ this'' -> ($mwrapped) ($(fieldFun ident) this'')) =<< I'.lift (I'.readIORef this')|]
            else let mapplied = runReader (let ?vars = localVars in foldlM
                                                    (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs|$acc <*> $targ|])
                                                    [hs|I'.pure $(HS.Var $ HS.UnQual $ HS.Ident mname)|]
                                                    args) formalParams
                     mwrapped = HS.Lambda (mkLoc p) [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs|awaitSugar' this (\ v'-> I'.writeIORef this' $(recordUpdate field)) obj' =<< I'.lift ($mapplied)|]
                 in [hs|(\ this'' -> ($mwrapped) ($(fieldFun ident) this'')) =<< I'.lift (I'.readIORef this')|]
      Just _ -> errorPos p "caller field not of interface type"
      Nothing -> errorPos p "no such field"
  ABS.ELit ABS.LNull -> errorPos p "null cannot be the object callee"
  _ -> errorPos p "current compiler limitation: the object callee cannot be an arbitrary pure-exp"


tFieldAss _ (ABS.L (_,field)) (ABS.ExpP pexp) = do
  (formalParams, localVars) <- getFormalLocal
  (_, _,onlyPureDeps) <- depends [pexp]
  pure $ maybeLift $
    if onlyPureDeps
    then let texp = runReader (let ?tyvars = [] in tPureExp pexp) formalParams
             recordModified = HS.RecUpdate [hs|this''|] [HS.FieldUpdate (HS.UnQual $ HS.Ident $ field ++ "'" ++ ?cname) $texp]
         in [hs|I'.writeIORef this' =<< ((\ this'' -> $recordModified) <$!> I'.readIORef this')|]
    else let texp = runReader (let ?vars = localVars in tStmExp pexp) formalParams
         in [hs|I'.writeIORef this' =<< ((\ this'' -> (\ v' -> $(recordUpdate field)) <$!> $texp) =<< I'.readIORef this')|]
  

tFieldAss _ i@(ABS.L (_,field)) (ABS.ExpE (ABS.New qcname args)) = do
  (formalParams, localVars) <- getFormalLocal
  (_,_,onlyPureDeps) <- depends args
  let (q, cname) = splitQU qcname
      smartCon = HS.Var $ (if null q then HS.UnQual else HS.Qual $ HS.ModuleName q) $ HS.Ident $ "smart'" ++ cname
      initFun = HS.Var $ (if null q then HS.UnQual else HS.Qual $ HS.ModuleName q) $ HS.Ident $ "init'" ++ cname
      Just (ABS.TSimple qtyp) = M.lookup i ?fields 
      recordUpdateCast = HS.RecUpdate [hs|this''|] [HS.FieldUpdate (HS.UnQual $ HS.Ident $ field ++ "'" ++ ?cname) [hs|$(HS.Var $ HS.UnQual $ HS.Ident $ showQU qtyp) v'|]]
  pure $ maybeLift $ 
    if onlyPureDeps
    then let smartApplied = runReader (let ?tyvars = [] in foldlM
                                                         (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                         smartCon
                                                         args) formalParams
         in [hs|I'.writeIORef this' =<< ((\ this'' -> (\ v' -> $recordUpdateCast) <$!> new $initFun $smartApplied) =<< I'.readIORef this')|]
    else let smartApplied = runReader (let ?vars = localVars in foldlM
                                               (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs|$acc <*> $targ|])
                                               [hs|I'.pure $smartCon|]
                                               args) formalParams
         in [hs|I'.writeIORef this' =<< ((\ this'' -> (\ v' -> $recordUpdateCast) <$!> (new $initFun =<< $smartApplied)) =<< I'.readIORef this')|]

tFieldAss _ i@(ABS.L (_,field)) (ABS.ExpE (ABS.NewLocal qcname args)) = do
  (formalParams, localVars) <- getFormalLocal
  (_,_,onlyPureDeps) <- depends args
  let (q, cname) = splitQU qcname
      smartCon = HS.Var $ (if null q then HS.UnQual else HS.Qual $ HS.ModuleName q) $ HS.Ident $ "smart'" ++ cname
      initFun = HS.Var $ (if null q then HS.UnQual else HS.Qual $ HS.ModuleName q) $ HS.Ident $ "init'" ++ cname
      Just (ABS.TSimple qtyp) = M.lookup i ?fields 
      recordUpdateCast = HS.RecUpdate [hs|this''|] [HS.FieldUpdate (HS.UnQual $ HS.Ident $ field ++ "'" ++ ?cname) [hs|$(HS.Var $ HS.UnQual $ HS.Ident $ showQU qtyp) v'|]]
  pure $ maybeLift $ 
    if onlyPureDeps
    then let smartApplied = runReader (let ?tyvars = [] in foldlM
                                                         (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                         smartCon
                                                         args) formalParams
         in [hs|I'.writeIORef this' =<<
                                 ((\ this'' -> (\ v' -> $recordUpdateCast) <$!> newlocal' this $initFun $smartApplied) =<< I'.readIORef this')|]
    else let smartApplied = runReader (let ?vars = localVars in foldlM
                                               (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs|$acc <*> $targ|])
                                               [hs|I'.pure $smartCon|]
                                               args) formalParams
         in [hs|I'.writeIORef this' =<< ((\ this'' -> (\ v' -> $recordUpdateCast) <$!> (newlocal' this $initFun =<< $smartApplied)) =<< I'.readIORef this')|]

tFieldAss a i@(ABS.L (_,field)) (ABS.ExpE (ABS.SyncMethCall pexp (ABS.L (p,mname)) args)) =
  case pexp of
   ABS.EVar ident@(ABS.L (_,calleeVar)) -> do
    (formalParams, localVars) <- getFormalLocal
    scopeLevels <- get
    case M.lookup ident (M.unions scopeLevels) of -- check type in the scopes
      Just (ABS.TSimple qtyp) -> do -- only interface type
          (_,_,onlyPureDeps) <- depends args
          let (prefix, iident) = splitQU qtyp
              iname = (if null prefix then HS.UnQual else HS.Qual $ HS.ModuleName prefix) $ HS.Ident iident
          pure $
            if onlyPureDeps
            then let mapplied = runReader (let ?tyvars = [] in foldlM
                                                              (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                              (HS.Var $ HS.UnQual $ HS.Ident mname)
                                                              args) formalParams
                     mwrapped = HS.Lambda (mkLoc p) [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs|sync' this obj' $mapplied|]
                 in if ident `M.member` formalParams
                    then [hs|(I'.lift . I'.writeIORef this') =<< 
                               (( \ this'' -> (\ v' -> $(recordUpdate field)) <$!> (($mwrapped) $(HS.Var $ HS.UnQual $ HS.Ident calleeVar)))
                                =<< I'.lift (I'.readIORef this'))|]
                    else [hs|(I'.lift . I'.writeIORef this') =<< 
                              (( \ this'' -> 
                                     (\ v' -> $(recordUpdate field)) <$!> (($mwrapped) =<< I'.lift (I'.readIORef $(HS.Var $ HS.UnQual $ HS.Ident calleeVar)))
                               ) =<< I'.lift (I'.readIORef this'))|]
            else let mapplied = runReader (let ?vars = localVars in foldlM
                                                         (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs|$acc <*> $targ|])
                                                         [hs|I'.pure $(HS.Var $ HS.UnQual $ HS.Ident mname)|]
                                                         args) formalParams
                     mwrapped = HS.Lambda (mkLoc p) [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs|sync' this obj' =<< I'.lift ($mapplied)|]
                 in if ident `M.member` formalParams
                    then [hs|(I'.lift . I'.writeIORef this') =<< 
                               (( \ this'' -> (\ v' -> $(recordUpdate field)) <$!> (($mwrapped) $(HS.Var $ HS.UnQual $ HS.Ident calleeVar)))
                                =<< I'.lift (I'.readIORef this'))|]
                    else [hs|(I'.lift . I'.writeIORef this') =<< 
                              (( \ this'' -> 
                                     (\ v' -> $(recordUpdate field)) <$!> (($mwrapped) =<< I'.lift (I'.readIORef $(HS.Var $ HS.UnQual $ HS.Ident calleeVar)))
                               ) =<< I'.lift (I'.readIORef this'))|]
      Just _ ->  errorPos p "caller variable not of interface type"
      Nothing -> if ident `M.member` ?fields
                 then tFieldAss a i (ABS.ExpE (ABS.SyncMethCall (ABS.EField ident) (ABS.L (p,mname)) args)) -- rewrite:this.var
                 else errorPos p "cannot find variable"
   ABS.EField ident ->
     case M.lookup ident ?fields of
      Just (ABS.TSimple qtyp) -> do -- only interface type
          (formalParams, localVars) <- getFormalLocal
          (_,_,onlyPureDeps) <- depends args
          let (prefix, iident) = splitQU qtyp
              iname = (if null prefix then HS.UnQual else HS.Qual $ HS.ModuleName prefix) $ HS.Ident iident
          pure $
            if onlyPureDeps
            then let mapplied = runReader (let ?tyvars = [] in foldlM
                                                         (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                         (HS.Var $ HS.UnQual $ HS.Ident mname) args) formalParams
                     mwrapped = HS.Lambda (mkLoc p) [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs|sync' this obj' $mapplied|]
                 in [hs|(I'.lift . I'.writeIORef this') =<< ((\ this'' -> (\ v' -> $(recordUpdate field)) <$!> ($mwrapped ($(fieldFun ident) this''))) =<< I'.lift (I'.readIORef this'))|]
            else let mapplied = runReader (let ?vars = localVars in foldlM
                                                    (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs|$acc <*> $targ|])
                                                    [hs|I'.pure $(HS.Var $ HS.UnQual $ HS.Ident mname)|]                                                    
                                                    args) formalParams
                     mwrapped = HS.Lambda (mkLoc p) [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs|sync' this obj' =<< I'.lift ($mapplied)|]
                 in [hs|(I'.lift . I'.writeIORef this') =<< ((\ this'' -> (\ v' -> $(recordUpdate field)) <$!> ($mwrapped ($(fieldFun ident) this''))) =<< I'.lift (I'.readIORef this'))|]
      Just _ -> errorPos p "caller field not of interface type"
      Nothing -> errorPos p "no such field"
   ABS.ELit ABS.LNull -> errorPos p "null cannot be the object callee"
   _ -> errorPos p "current compiler limitation: the object callee cannot be an arbitrary pure-exp"

tFieldAss _ (ABS.L (_,field)) (ABS.ExpE (ABS.ThisSyncMethCall (ABS.L (_,mname)) args)) = do
  (formalParams, localVars) <- getFormalLocal
  (_,_,onlyPureDeps) <- depends args
  pure $
    if onlyPureDeps
    then let mapplied = runReader (let ?tyvars = [] in foldlM
                                                      (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                      (maybeMangleCall mname)
                                                      args) formalParams
         in [hs|(I'.lift . I'.writeIORef this') =<< ((\ this'' -> (\ v' -> $(recordUpdate field)) <$!> (this <..> $mapplied)) =<< I'.lift (I'.readIORef this')) |]
    else let mapplied = runReader (let ?vars = localVars in foldlM
                                                 (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs|$acc <*> $targ|])
                                                 ((\ e-> [hs|I'.pure $e|]) (maybeMangleCall mname))
                                                 args) formalParams
         in [hs|(I'.lift . I'.writeIORef this') =<< ((\ this'' -> (\ v' -> $(recordUpdate field)) <$!> ((this <..>) =<< I'.lift ($mapplied))) =<< I'.lift (I'.readIORef this'))|]

tFieldAss a i@(ABS.L (_,field)) (ABS.ExpE (ABS.AsyncMethCall pexp (ABS.L (p,mname)) args)) =
 case pexp of
  ABS.ELit ABS.LThis -> do
    (formalParams, localVars) <- getFormalLocal
    (_,_,onlyPureDeps) <- depends args
    pure $ maybeLift $
      if onlyPureDeps
      then let mapplied = runReader (let ?tyvars = [] in foldlM
                                                 (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                 (maybeMangleCall mname)
                                                 args) formalParams
           in [hs|I'.writeIORef this' =<< ((\ this'' -> (\ v' -> $(recordUpdate field)) <$!> (this <!> $mapplied)) =<< I'.readIORef this')|]
      else let mapplied = runReader (let ?vars = localVars in foldlM
                                                                        (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs|$acc <*> $targ|])
                                                                        ((\ e-> [hs|I'.pure $e|]) (maybeMangleCall mname))
                                                                        args) formalParams
           in [hs|I'.writeIORef this' =<< ((\ this'' -> (\ v' -> $(recordUpdate field)) <$!> ((this <!>) =<< $mapplied)) =<< I'.readIORef this')|]
  ABS.EVar ident@(ABS.L (_, calleeVar)) -> do
    (formalParams, localVars) <- getFormalLocal
    scopeLevels <- get
    case M.lookup ident $ M.unions scopeLevels of -- check type in the scopes
      Just (ABS.TSimple qtyp) -> do -- only interface type
          (_,_,onlyPureDeps) <- depends args
          let (prefix, iident) = splitQU qtyp
              iname = (if null prefix then HS.UnQual else HS.Qual $ HS.ModuleName prefix) $ HS.Ident iident
          pure $ maybeLift $
            if onlyPureDeps
            then let mapplied = runReader (let ?tyvars = [] in foldlM
                                                         (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                         (HS.Var $ HS.UnQual $ HS.Ident mname) args) formalParams
                     mwrapped = HS.Lambda (mkLoc p) [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs|(obj' <!> $mapplied)|]
                 in if ident `M.member` formalParams
                    then [hs|
                              I'.writeIORef this' =<< (\ this'' -> 
                                                        (\ v' -> $(recordUpdate field)) <$!> (($mwrapped) 
                                                                                   $(HS.Var $ HS.UnQual $ HS.Ident calleeVar))) 
                                                        =<< I'.readIORef this'|]
                    else [hs|
                              I'.writeIORef this' =<< (\ this'' -> 
                                                        (\ v' -> $(recordUpdate field)) <$!> (($mwrapped) 
                                                                                   =<< I'.readIORef $(HS.Var $ HS.UnQual $ HS.Ident calleeVar))) 
                                                        =<< I'.readIORef this'|]
            else let mapplied = runReader (let ?vars = localVars in foldlM
                                                                            (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs|$acc <*> $targ|])
                                                                            [hs|I'.pure $(HS.Var $ HS.UnQual $ HS.Ident mname)|]
                                                                            args) formalParams
                     mwrapped = HS.Lambda (mkLoc p) [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs|(obj' <!>) =<< $mapplied|]
                 in if ident `M.member` formalParams
                    then [hs|I'.writeIORef this' =<< (\ this'' -> 
                                                        (\ v' -> $(recordUpdate field)) <$!> (($mwrapped) 
                                                                                   $(HS.Var $ HS.UnQual $ HS.Ident calleeVar))) 
                                                        =<< I'.readIORef this'|]
                    else [hs|I'.writeIORef this' =<< (\ this'' -> 
                                                        (\ v' -> $(recordUpdate field)) <$!> (($mwrapped) 
                                                                                   =<< I'.readIORef $(HS.Var $ HS.UnQual $ HS.Ident calleeVar))) 
                                                        =<< I'.readIORef this'|]
      Nothing -> if ident `M.member` ?fields
                 then tFieldAss a i (ABS.ExpE (ABS.AsyncMethCall (ABS.EField ident) (ABS.L (p,mname)) args))
                 else errorPos p "cannot find variable"
      _ -> errorPos p "invalid object callee type"
  ABS.EField ident ->
    case M.lookup ident ?fields of
      Just (ABS.TSimple qtyp) -> do -- only interface type
          (formalParams, localVars) <- getFormalLocal
          (_,_,onlyPureDeps) <- depends args
          let (prefix, iident) = splitQU qtyp
              iname = (if null prefix then HS.UnQual else HS.Qual $ HS.ModuleName prefix) $ HS.Ident iident
          pure $ maybeLift $
            if onlyPureDeps
            then let mapplied = runReader (let ?tyvars = [] in foldlM
                                                         (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                         (HS.Var $ HS.UnQual $ HS.Ident mname) args) formalParams
                     mwrapped = HS.Lambda (mkLoc p) [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs|(obj' <!> $mapplied)|]
                 in [hs|I'.writeIORef this' =<< (\ this'' -> (\ v' -> $(recordUpdate field)) <$!> ($mwrapped ($(fieldFun ident) this''))) =<< I'.readIORef this'|]
            else let mapplied = runReader (let ?vars = localVars in foldlM
                                                    (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs|$acc <*> $targ|])
                                                    [hs|I'.pure $(HS.Var $ HS.UnQual $ HS.Ident mname)|]                                                    
                                                    args) formalParams
                     mwrapped = HS.Lambda (mkLoc p) [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs|(obj' <!>) =<< $mapplied|]
                 in [hs|I'.writeIORef this' =<< (\ this'' -> (\ v' -> $(recordUpdate field)) <$!> ($mwrapped ($(fieldFun ident) this''))) =<< I'.readIORef this'|]
      Just _ -> errorPos p "caller field not of interface type"
      Nothing -> errorPos p "no such field"
  ABS.ELit ABS.LNull -> errorPos p "null cannot be the object callee"
  _ -> errorPos p "current compiler limitation: the object callee cannot be an arbitrary pure-exp"


tFieldAss _ (ABS.L (_,field)) (ABS.ExpE (ABS.Get pexp)) = do
  (formalParams, localVars) <- getFormalLocal
  (_,_,onlyPureDeps) <- depends [pexp]
  let sureLift = if ?isInit then error "get not allowed inside init" else (\e -> [hs|I'.lift ($e)|])
  pure $ sureLift $
    if onlyPureDeps
    then let texp = runReader (let ?tyvars = [] in tPureExp pexp) formalParams
         in [hs|I'.writeIORef this' =<< ((\ this'' -> (\ v' -> $(recordUpdate field)) <$!> get $texp) =<< I'.readIORef this')|]
    else let texp = runReader (let ?vars = localVars in tStmExp pexp) formalParams
         in [hs|I'.writeIORef this' =<< ((\ this'' -> (\ v' -> $(recordUpdate field)) <$!> (get =<< $texp)) =<< I'.readIORef this')|]

tFieldAss _ (ABS.L (_,field)) (ABS.ExpE (ABS.ProTry pexp)) = do
    (formalParams, localVars) <- getFormalLocal
    (_,__,onlyPureDeps) <- depends [pexp]
    pure $ maybeLift $
      if onlyPureDeps
      then let texp = runReader (let ?tyvars = [] in tPureExp pexp) formalParams
           in [hs|I'.writeIORef this' =<< ((\ this'' -> (\ v' -> $(recordUpdate field)) <$!> pro_try $texp) =<< I'.readIORef this')|]
      else let texp = runReader (let ?vars = localVars in tStmExp pexp) formalParams
           in [hs|I'.writeIORef this' =<< ((\ this'' -> (\ v' -> $(recordUpdate field)) <$!> (pro_try =<< $texp)) =<< I'.readIORef this')|]

tFieldAss _ (ABS.L (_,field)) (ABS.ExpE ABS.ProNew) =
  pure $ maybeLift [hs|I'.writeIORef this' =<< ((\ this'' -> (\ v' -> $(recordUpdate field)) <$!> pro_new) =<< I'.readIORef this')|]

tFieldAss _ (ABS.L (_,field)) (ABS.ExpE ABS.Now) =
  pure $ maybeLift [hs|I'.writeIORef this' =<< ((\ this'' -> (\ v' -> $(recordUpdate field)) <$!> now) =<< I'.readIORef this')|]

tFieldAss _ (ABS.L (_,field)) (ABS.ExpE ABS.Readln) =
  pure $ maybeLift [hs|I'.writeIORef this' =<< ((\ this'' -> (\ v' -> $(recordUpdate field)) <$!> readln) =<< I'.readIORef this')|]



tStm :: (?absFileName::String, ?cAloneMethods::[String], ?cname::String, ?fields::ScopeLVL, ?isInit::Bool, ?st::SymbolTable)
     => ABS.AnnStm
     -> BlockScope [HS.Stmt]

-- sdecass awaitmethcall has to be treated specially
tStm (ABS.AnnStm a (ABS.SDecAss t i@(ABS.L (p,n)) e@(ABS.ExpE (ABS.AwaitMethCall _ _ _)))) = do
 addToScope t i 
 awaitCall <- tAss a t i e
 pure [ HS.Generator (mkLoc p) (HS.PatTypeSig noLoc' (HS.PVar $ HS.Ident n) (HS.TyApp (HS.TyCon $ HS.UnQual $ HS.Ident "IORef'") (tType t))) 
                          [hs| I'.lift (I'.newIORef I'.undefined)|]
      , HS.Qualifier awaitCall
      ]
-- rest
tStm (ABS.AnnStm annots (ABS.SDecAss t i@(ABS.L (p,n)) e)) = do
  addToScope t i
  pure . HS.Generator 
    (mkLoc p) 
    (HS.PatTypeSig noLoc' (HS.PVar $ HS.Ident n) (HS.TyApp (HS.TyCon $ HS.UnQual $ HS.Ident "IORef'") (tType t)))
     <$> tDecAss annots t i e


--- DISPATCHER: LOCAL-VARIABLE OR FIELD ASSIGMENT

tStm (ABS.AnnStm a (ABS.SAss i e)) = do
  scope <- M.unions <$> get
  pure . HS.Qualifier <$> 
    case M.lookup i scope of
      Just typ -> tAss a typ i e 
      Nothing -> if i `M.member` ?fields
                 then tFieldAss a i e -- normalize it to fieldass
                 else error "not in scope"

-- DISPATCHER: FIELD_ASSIGNMENT
tStm (ABS.AnnStm a (ABS.SFieldAss i e)) = pure . HS.Qualifier <$> tFieldAss a i e

------------------------- RETURN , STANDALONE EXPRESSION

tStm (ABS.AnnStm _ (ABS.SReturn (ABS.ExpE eexp))) = pure . HS.Qualifier <$> tEffExp eexp False -- keep the result
tStm (ABS.AnnStm _ (ABS.SReturn (ABS.ExpP pexp))) = do
  (formalParams, localVars) <- getFormalLocal
  (_, fields,onlyPureDeps) <- depends [pexp]
  pure [HS.Qualifier $ maybeLift $ maybeThis fields $        -- keep the result
    if onlyPureDeps
    then let texp = runReader (let ?tyvars = [] in tPureExp pexp) formalParams
         in [hs|I'.pure $texp|]
    else let texp = runReader (let ?vars = localVars in tStmExp pexp) formalParams
         in texp]

tStm (ABS.AnnStm _ (ABS.SExp (ABS.ExpE eexp))) = pure . HS.Generator noLoc' HS.PWildCard <$> tEffExp eexp True -- throw away the result
tStm (ABS.AnnStm _ (ABS.SExp (ABS.ExpP pexp))) = do
  (formalParams, localVars) <- getFormalLocal
  (_, fields,onlyPureDeps) <- depends [pexp]
  pure [HS.Generator noLoc' HS.PWildCard $ maybeLift $ maybeThis fields $ -- throw away the result
    if onlyPureDeps
    then let texp = runReader (let ?tyvars = [] in tPureExp pexp) formalParams
         in [hs|I'.pure $texp|]
    else let texp = runReader (let ?vars = localVars in tStmExp pexp) formalParams
         in texp ]


---- DECLARATION

tStm (ABS.AnnStm _ (ABS.SDec t i@(ABS.L (p,n)))) = do
  addToScope t i
  pure [HS.Generator (mkLoc p) 
          (HS.PatTypeSig noLoc' (HS.PVar $ HS.Ident n) (HS.TyApp (HS.TyCon $ HS.UnQual $ HS.Ident "IORef'") (tType t))) $ maybeLift $
          case t of
            -- it is an unitialized future (set to newEmptyMVar)
            ABS.TPoly (ABS.U_ (ABS.U (_,"Fut")))  _ -> [hs|I'.newIORef nullFuture'|]
            -- it may be an object (set to null) or foreign (set to undefined)
            _ -> let
                  qtyp = case t of
                           ABS.TSimple qtyp' -> qtyp'
                           ABS.TPoly qtyp' _ -> qtyp'
                           ABS.TInfer -> todo
                  (prefix, ident) = splitQU qtyp
                  Just (SV symbolType _) = if null prefix
                                           then snd <$> find (\ (SN ident' modul,_) -> ident == ident' && maybe True (not . snd) modul) (M.assocs ?st)
                                           else M.lookup (SN ident (Just (prefix, True))) ?st 
                in case symbolType of
                     Interface _ _ -> [hs|I'.newIORef ($(HS.Var $ HS.UnQual $ HS.Ident $ showQU qtyp) null)|]  -- o :: IORef Interf <- null
                     Foreign -> [hs|I'.newIORef (I'.error "foreign object not initialized")|] -- undefined if foreign
                     _ -> errorPos p "A field must be initialised if it is not of a reference type"
         ]


-- CONCURRENCY STATEMENTS
-------------------------

tStm (ABS.AnnStm _ ABS.SSuspend) = pure [HS.Qualifier [hs|suspend this|]]

tStm (ABS.AnnStm _ (ABS.SAwait ag)) = do
  let (futureGuards, boolGuards) = splitGuard ag
  tfguards <- mapM tGuard futureGuards   -- sequentialize: await f1guard? ; await f2guard?;
  tbguards <- if null boolGuards
             then pure []                           
             else tGuard (foldl1 (\ (ABS.GExp exp1) (ABS.GExp exp2) -> ABS.GExp $ exp1 `ABS.EAnd` exp2) boolGuards) -- combine bguards with boolean AND
  pure $ concat tfguards ++ tbguards
  where
    splitGuard :: ABS.AwaitGuard -> ([ABS.AwaitGuard], [ABS.AwaitGuard])
    splitGuard g = splitGuard' g ([],[])
    splitGuard' g (fs,as)= case g of
                             ABS.GFutField _ -> (g:fs,as)
                             ABS.GFut _ -> (g:fs,as)
                             ABS.GDuration _ _ -> (g:fs, as)
                             ABS.GExp _ -> (fs,g:as)
                             ABS.GAnd gl gr -> let 
                                                   (fsl,asl) = splitGuard gl
                                                   (fsr,asr) = splitGuard gr 
                                                  in (fsl++fs++fsr,asl++as++asr)
    tGuard (ABS.GAnd _ _ ) = total
    tGuard (ABS.GFut var@(ABS.L (_, fname))) = do
      (formalParams, localVars) <- getFormalLocal
      if var `M.member` formalParams 
        then  pure [HS.Qualifier [hs|awaitFuture' this $(HS.Var $ HS.UnQual $ HS.Ident fname)|]]
        else if var `M.member` localVars
             then pure [HS.Qualifier [hs|awaitFuture' this =<< I'.lift (I'.readIORef $(HS.Var $ HS.UnQual $ HS.Ident fname))|]]
             else tGuard (ABS.GFutField var) -- try as field-future

    tGuard (ABS.GDuration pexp1 pexp2) = do
      (formalParams, localVars) <- getFormalLocal
      (_,fields,onlyPureDeps) <- depends [pexp1,pexp2]
      pure [HS.Qualifier $ maybeThis fields $
         if onlyPureDeps
         then let texp1 = runReader (let ?tyvars = [] in tPureExp pexp1) formalParams
                  texp2 = runReader (let ?tyvars = [] in tPureExp pexp2) formalParams
              in [hs|awaitDuration' this $texp1 $texp2|]
         else let texp1 = runReader (let ?vars = localVars in tStmExp pexp1) formalParams
                  texp2 = runReader (let ?vars = localVars in tStmExp pexp2) formalParams
              in [hs|(\ e1' -> awaitDuration' this e1' =<< $texp2) =<< $texp1|] ]

    -- currently, no solution to the cosimo problem
    tGuard (ABS.GFutField f) = pure [HS.Qualifier [hs|(awaitFuture' this . $(fieldFun f)) =<< I'.lift (I'.readIORef this')|]]

    tGuard (ABS.GExp pexp) = do
      (locals, fields,onlyPureDeps) <- depends [pexp]
      (formalParams, _) <- getFormalLocal
      scopeLevels <- get
      pure [HS.Qualifier $
        if null fields 
        then warnPos (1,1) "the calling process and its parent(s) may block" $
            if onlyPureDeps
            then let texp = runReader (let ?tyvars = [] in tPureExp pexp) formalParams
                 in [hs|if $texp then I'.pure () else awaitDuration' this 2147 2147|] -- simulate blocking by waiting for long (32-bit systems allows max int32 as 2147
            else let texp = runReader (let ?tyvars = [] in tPureExp pexp) (M.unions scopeLevels)
                     expWrapped = foldl (\ acc (ABS.L (_, nextVar)) -> 
                                                    let nextIdent = HS.Ident nextVar 
                                                    in [hs|(\ ((nextIdent)) -> $acc) =<< I'.readIORef $(HS.Var $ HS.UnQual nextIdent)|])
                                         [hs|I'.pure (\ this'' -> $texp)|]
                                         (nub locals)
                  in [hs|(\case {True -> I'.pure (); False -> awaitDuration' this 2147 2147}) =<< I'.lift ($expWrapped)|] 
        else if onlyPureDeps
             then let texp = runReader (let ?tyvars = [] in tPureExp pexp) formalParams
                  in [hs|awaitBool' this (\ this'' -> $texp)|]
             else let texp = runReader (let ?tyvars = [] in tPureExp pexp) (M.unions scopeLevels)
                      expWrapped = foldl (\ acc (ABS.L (_, nextVar)) -> 
                                                    let nextIdent = HS.Ident nextVar 
                                                    in [hs|(\ ((nextIdent)) -> $acc) =<< I'.readIORef $(HS.Var $ HS.UnQual nextIdent)|])
                                         [hs|I'.pure (\ this'' -> $texp)|]
                                         (nub locals)
                  in [hs|awaitBool' this =<< I'.lift ($expWrapped)|]]

tStm (ABS.AnnStm _ (ABS.SGive pexp1 pexp2)) = do
  (formalParams, localVars) <- getFormalLocal
  (_,fields,onlyPureDeps) <- depends [pexp1,pexp2]
  pure [HS.Qualifier $ maybeLift $ maybeThis fields $
    if onlyPureDeps
    then let texp1 = runReader (let ?tyvars = [] in tPureExp pexp1) formalParams
             texp2 = runReader (let ?tyvars = [] in tPureExp pexp2) formalParams
         in [hs|pro_give $texp1 $texp2|]
    else let texp1 = runReader (let ?vars = localVars in tStmExp pexp1) formalParams
             texp2 = runReader (let ?vars = localVars in tStmExp pexp2) formalParams
         in [hs|(\ e1' -> pro_give e1' =<< $texp2) =<< $texp1|] ]


-- CONTROL FLOW STATEMENTS
--------------------------

tStm (ABS.AnnStm _ (ABS.SWhile pexp stmBody)) = do
  (formalParams, localVars) <- getFormalLocal
  (_, fields,_) <- depends [pexp]
  [HS.Qualifier tbody] <- tStm $ case stmBody of
                                  ABS.AnnStm _ (ABS.SBlock _) -> stmBody
                                  singleStm -> ABS.AnnStm [] (ABS.SBlock [singleStm]) -- if single statement, wrap it in a new DO-scope
  let texp = runReader (let ?vars = localVars in tStmExp pexp) formalParams  -- only treat it as StmExp
      whileFun = if ?isInit then [hs|while'|] else [hs|while|]
  pure [HS.Qualifier [hs|$whileFun $(maybeThis fields texp) $tbody|]]

tStm (ABS.AnnStm _ (ABS.SIf pexp stmThen)) = do
  (formalParams, localVars) <- getFormalLocal
  (_, fields,onlyPureDeps) <- depends [pexp]
  tthen <- (\case 
           [] -> [hs|I'.pure ()|]
           [HS.Qualifier tthen'] -> tthen'
           _ -> total) <$> (tStm $ ABS.AnnStm [] $ case stmThen of
                                                        ABS.SBlock _ -> stmThen
                                                        singleStm -> ABS.SBlock [ABS.AnnStm [] singleStm]) -- if single statement, wrap it in a new DO-scope
  pure $ if onlyPureDeps
         then let tpred = runReader (let ?tyvars = [] in tPureExp pexp) formalParams
                  maybeWrapThis = if null fields 
                                  then id 
                                  else if ?isInit 
                                       then (\ e -> [hs|(\ this'' -> $e) =<< I'.readIORef this'|])
                                       else (\ e -> [hs|(\ this'' -> $e) =<< I'.lift (I'.readIORef this')|])
              in [HS.Qualifier $ maybeWrapThis [hs|I'.when $tpred $tthen|]]
         else let tpred = runReader (let ?vars = localVars in tStmExp pexp) formalParams
              in [ HS.Generator noLoc' (HS.PVar $ HS.Ident "when'") (maybeLift $ maybeThis fields tpred)
                 , HS.Qualifier [hs|I'.when when' $tthen|]]

tStm (ABS.AnnStm _ (ABS.SIfElse pexp stmThen stmElse)) = do
  (formalParams, localVars) <- getFormalLocal
  (_, fields,onlyPureDeps) <- depends [pexp]
  tthen <- (\case 
           [] -> [hs|I'.pure ()|]
           [HS.Qualifier tthen'] -> tthen'
           _ -> total) <$> (tStm $ ABS.AnnStm [] $ case stmThen of
                                                        ABS.SBlock _ -> stmThen
                                                        singleStm -> ABS.SBlock [ABS.AnnStm [] singleStm]) -- if single statement, wrap it in a new DO-scope
  telse <- (\case 
           [] -> [hs|I'.pure ()|]
           [HS.Qualifier telse'] -> telse'
           _ -> total) <$> (tStm $ ABS.AnnStm [] $ case stmElse of
                                                        ABS.SBlock _ -> stmElse
                                                        singleStm -> ABS.SBlock [ABS.AnnStm [] singleStm]) -- if single statement, wrap it in a new DO-scope
      
  pure $ if onlyPureDeps
         then let tpred = runReader (let ?tyvars = [] in tPureExp pexp) formalParams
                  maybeWrapThis = if null fields 
                                  then id 
                                  else if ?isInit 
                                       then (\ e -> [hs|(\ this'' -> $e) =<< I'.readIORef this'|])
                                       else (\ e -> [hs|(\ this'' -> $e) =<< I'.lift (I'.readIORef this')|])
              in [HS.Qualifier $ maybeWrapThis [hs|if $tpred then $tthen else $telse|]]
         else let tpred = runReader (let ?vars = localVars in tStmExp pexp) formalParams
              in [ HS.Generator noLoc' (HS.PVar $ HS.Ident "if'") (maybeLift $ maybeThis fields tpred)
                 , HS.Qualifier [hs|if if' then $tthen else $telse|]]


tStm (ABS.AnnStm _ (ABS.SCase pexp branches)) = do
  (formalParams, localVars) <- getFormalLocal
  (_,fields,onlyPureDeps) <- depends [pexp]
  tbranches <- mapM (\ (ABS.SCaseBranch pat branchStm) -> do
                                                         tstm <- (\case 
                                                                    [] -> [hs|I'.pure ()|]
                                                                    [HS.Qualifier tblock'] -> tblock'
                                                                    _ -> total) 
                                                                 <$> tStm (case branchStm of
                                                                              block@(ABS.AnnStm _ (ABS.SBlock _)) -> block
                                                                              stm -> ABS.AnnStm [] (ABS.SBlock [stm])) -- if single statement, wrap it in a new DO-scope
                                                         pure $ HS.Alt noLoc' (tPattern pat) (HS.UnGuardedRhs tstm) Nothing
                    ) branches
  pure $ if onlyPureDeps
         then let tpred = runReader (let ?tyvars = [] in tPureExp pexp) formalParams
                  maybeWrapThis = if null fields 
                                  then id 
                                  else if ?isInit 
                                       then (\ e -> [hs|(\ this'' -> $e) =<< I'.readIORef this'|])
                                       else (\ e -> [hs|(\ this'' -> $e) =<< I'.lift (I'.readIORef this')|])
              in [HS.Qualifier $ maybeWrapThis $ HS.Case tpred tbranches]
         else let tpred = runReader (let ?vars = localVars in tStmExp pexp) formalParams
              in [ HS.Generator noLoc' (HS.PVar $ HS.Ident "case'") (maybeLift $ maybeThis fields tpred)
                 , HS.Qualifier $ HS.Case [hs|case'|] tbranches ]


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
                       HS.Generator _ _ _ ->  tstms ++ [HS.Qualifier $ [hs|I'.pure ()|]]
                       _ -> tstms]


tStm (ABS.AnnStm _ (ABS.SPrint pexp)) = do
  (formalParams, localVars) <- getFormalLocal
  (_, fields,onlyPureDeps) <- depends [pexp]
  pure [HS.Qualifier $ maybeLift $ 
    if onlyPureDeps
    then let texp = runReader (let ?tyvars = [] in tPureExp pexp) formalParams
         in maybeThis fields [hs|print $texp|]
    else let texp = runReader (let ?vars = localVars in tStmExp pexp) formalParams
         in [hs|print =<< $(maybeThis fields texp)|] ]


tStm (ABS.AnnStm _ (ABS.SPrintln pexp)) = do
  (formalParams, localVars) <- getFormalLocal
  (_, fields,onlyPureDeps) <- depends [pexp]
  pure [HS.Qualifier $ maybeLift $ 
    if onlyPureDeps
    then let texp = runReader (let ?tyvars = [] in tPureExp pexp) formalParams
         in maybeThis fields [hs|println $texp|]
    else let texp = runReader (let ?vars = localVars in tStmExp pexp) formalParams
         in [hs|println =<< $(maybeThis fields texp)|] ]


tStm (ABS.AnnStm _ (ABS.SDuration pexp1 pexp2)) = do
  (formalParams, localVars) <- getFormalLocal
  (_,fields,onlyPureDeps) <- depends [pexp1,pexp2]
  pure [HS.Qualifier $ maybeLift $ maybeThis fields $
         if onlyPureDeps
         then let texp1 = runReader (let ?tyvars = [] in tPureExp pexp1) formalParams
                  texp2 = runReader (let ?tyvars = [] in tPureExp pexp2) formalParams
              in [hs|duration $texp1 $texp2|]
         else let texp1 = runReader (let ?vars = localVars in tStmExp pexp1) formalParams
                  texp2 = runReader (let ?vars = localVars in tStmExp pexp2) formalParams
              in [hs|(\ e1' -> duration e1' =<< $texp2) =<< $texp1|] ]


-- EXCEPTION STATEMENTS
-------------------------

tStm (ABS.AnnStm _ (ABS.SAssert pexp)) = do
  (formalParams, localVars) <- getFormalLocal
  (_, fields,onlyPureDeps) <- depends [pexp]
  pure [HS.Qualifier $ maybeLift $ 
    if onlyPureDeps
    then let texp = runReader (let ?tyvars = [] in tPureExp pexp) formalParams
         in maybeThis fields [hs|assert $texp (I'.pure ())|]
    else let texp = runReader (let ?vars = localVars in tStmExp pexp) formalParams
         in [hs|(\ b' -> assert b' (I'.pure ())) =<< $(maybeThis fields texp)|] ]

tStm (ABS.AnnStm _ (ABS.SThrow pexp)) = do
  (formalParams, localVars) <- getFormalLocal
  (_, fields,onlyPureDeps) <- depends [pexp]
  pure [HS.Qualifier $ 
    if onlyPureDeps
    then let texp = runReader (let ?tyvars = [] in tPureExp pexp) formalParams
         in maybeThis fields [hs|throw $texp|]
    else let texp = runReader (let ?vars = localVars in tStmExp pexp) formalParams
         in maybeLift [hs|throw =<< $(maybeThis fields texp)|] ]

tStm (ABS.AnnStm _ (ABS.STryCatchFinally tryStm branches mfinally)) = do
                                   
  ttry <- (\case 
             [] -> [hs|I'.pure ()|]
             [HS.Qualifier tblock'] -> tblock'
             _ -> total) 
          <$> tStm (case tryStm of
                      block@(ABS.AnnStm _ (ABS.SBlock _)) -> block
                      stm -> ABS.AnnStm [] $ ABS.SBlock [stm]) -- if single statement, wrap it in a new DO-scope
  
  tbranches <- mapM (\ (ABS.SCaseBranch pat branchStm) -> do
                      tbstm <- (\case 
                                [] -> [hs|I'.pure ()|]
                                [HS.Qualifier tblock'] -> tblock'
                                _ -> total) 
                              <$> tStm (case branchStm of
                                          block@(ABS.AnnStm _ (ABS.SBlock _)) -> block
                                          stm -> ABS.AnnStm [] (ABS.SBlock [stm])) -- if single statement, wrap it in a new DO-scope
                      pure $ HS.App [hs|Handler'|] $ case pat of
                                -- a catch-all is a wrapped someexception
                                ABS.PWildCard -> [hs|\ (I'.SomeException _) -> Just ($tbstm)|]
                                _ -> HS.LCase [
                                        -- wrap the normal returned expression in a just
                                        HS.Alt noLoc' (tPattern pat) (HS.UnGuardedRhs [hs|Just ($tbstm)|]) Nothing
                                        -- pattern match fail, return nothing
                                      , HS.Alt noLoc' HS.PWildCard (HS.UnGuardedRhs [hs|Nothing|]) Nothing]                                  
                    ) branches

  tfin <- case mfinally of
            ABS.NoFinally -> pure id
            ABS.JustFinally finStm -> do
                         tblock <- (\case 
                                      [] -> [hs|I'.pure ()|]
                                      [HS.Qualifier tblock'] -> tblock'
                                      _ -> total) 
                                   <$> tStm (case finStm of
                                              block@(ABS.AnnStm _ (ABS.SBlock _)) -> block
                                              stm -> ABS.AnnStm [] $ ABS.SBlock [stm]) -- if single statement, wrap it in a new DO-scope
                         pure $ \ try_catch -> [hs|($try_catch) `finally` $tblock|]
  
  -- optionally wrap the try-catch in a finally block
  pure [HS.Qualifier $ tfin [hs|$ttry `catch` $(HS.List tbranches)|]]



-- (EFFECTFUL) EXPRESSIONS in statement world
---------------------------------------------

tEffExp :: ( ?absFileName:: String
           , ?st::SymbolTable
           , ?fields::ScopeLVL
           , ?cname::String
           , ?cAloneMethods::[String]
           , ?isInit::Bool) 
           => ABS.EffExp 
           -> Bool 
           -> BlockScope HS.Exp
tEffExp (ABS.New qcname args) _ = do
  (formalParams, localVars) <- getFormalLocal
  (_,fields,onlyPureDeps) <- depends args
  let (q, cname) = splitQU qcname
      smartCon = HS.Var $ (if null q then HS.UnQual else HS.Qual $ HS.ModuleName q) $ HS.Ident $ "smart'" ++ cname
      initFun = HS.Var $ (if null q then HS.UnQual else HS.Qual $ HS.ModuleName q) $ HS.Ident $ "init'" ++ cname
  pure $ maybeLift $ 
    if onlyPureDeps
    then let smartApplied = runReader (let ?tyvars = [] in foldlM
                                                        (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                        smartCon
                                                        args) formalParams
         in maybeThis fields [hs|new $initFun $smartApplied|]
    else let smartApplied = runReader (let ?vars = localVars in foldlM
                                                   (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs|$acc <*> $targ|])
                                                   [hs|I'.pure $smartCon|]
                                                   args) formalParams
         in [hs|new $initFun =<< $(maybeThis fields smartApplied)|]

tEffExp (ABS.NewLocal qcname args) _ = do
  (formalParams, localVars) <- getFormalLocal
  (_,fields,onlyPureDeps) <- depends args
  let (q, cname) = splitQU qcname
      smartCon = HS.Var $ (if null q then HS.UnQual else HS.Qual $ HS.ModuleName q) $ HS.Ident $ "smart'" ++ cname
      initFun = HS.Var $ (if null q then HS.UnQual else HS.Qual $ HS.ModuleName q) $ HS.Ident $ "init'" ++ cname
  pure $ maybeLift $ 
    if onlyPureDeps
    then let smartApplied = runReader (let ?tyvars = [] in foldlM
                                                        (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                        smartCon
                                                        args) formalParams
         in maybeThis fields [hs|newlocal' this $initFun $smartApplied|]
    else let smartApplied = runReader (let ?vars = localVars in foldlM
                                                   (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs|$acc <*> $targ|])
                                                   [hs|I'.pure $smartCon|]
                                                   args) formalParams
         in [hs|newlocal' this $initFun =<< $(maybeThis fields smartApplied)|]


tEffExp (ABS.SyncMethCall pexp (ABS.L (p,mname)) args) _isAlone = case pexp of
  ABS.EVar ident@(ABS.L (_,calleeVar)) -> do
    (formalParams, localVars) <- getFormalLocal
    scopeLevels <- get
    case M.lookup ident (M.unions scopeLevels) of -- check type in the scopes
      Just (ABS.TSimple qtyp) -> do -- only interface type
          (_,fields,onlyPureDeps) <- depends args
          let (prefix, iident) = splitQU qtyp
              iname = (if null prefix then HS.UnQual else HS.Qual $ HS.ModuleName prefix) $ HS.Ident iident
          pure $ maybeThisLifted fields $
            if onlyPureDeps
            then let mapplied = runReader (let ?tyvars = [] in foldlM
                                                         (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                         (HS.Var $ HS.UnQual $ HS.Ident mname)
                                                         args) formalParams
                     mwrapped = HS.Lambda (mkLoc p) [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs|sync' this obj' $mapplied|]
                 in if ident `M.member` formalParams
                    then [hs|($mwrapped) $(HS.Var $ HS.UnQual $ HS.Ident calleeVar)|]
                    else [hs|($mwrapped) =<< I'.lift (I'.readIORef $(HS.Var $ HS.UnQual $ HS.Ident calleeVar))|]
            else let mapplied = runReader (let ?vars = localVars in foldlM
                                                    (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs|$acc <*> $targ|])
                                                    [hs|I'.pure $(HS.Var $ HS.UnQual $ HS.Ident mname)|]
                                                    args) formalParams
                     mwrapped = HS.Lambda (mkLoc p) [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs|sync' this obj' =<< I'.lift ($mapplied)|]
                 in if ident `M.member` formalParams
                    then [hs|($mwrapped) $(HS.Var $ HS.UnQual $ HS.Ident calleeVar)|]
                    else [hs|($mwrapped) =<< I'.lift (I'.readIORef $(HS.Var $ HS.UnQual $ HS.Ident calleeVar))|]
      Just _ ->  errorPos p "caller variable not of interface type"
      Nothing -> if ident `M.member` ?fields
                then tEffExp (ABS.SyncMethCall (ABS.EField ident) (ABS.L (p,mname)) args) _isAlone -- rewrite it to this.var
                else errorPos p "cannot find variable"
  ABS.EField ident ->
    case M.lookup ident ?fields of
      Just (ABS.TSimple qtyp) -> do -- only interface type
          (formalParams, localVars) <- getFormalLocal
          (_,_,onlyPureDeps) <- depends args
          let (prefix, iident) = splitQU qtyp
              iname = (if null prefix then HS.UnQual else HS.Qual $ HS.ModuleName prefix) $ HS.Ident iident
          pure $ 
            if onlyPureDeps
            then let mapplied = runReader (let ?tyvars = [] in foldlM
                                                         (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                         (HS.Var $ HS.UnQual $ HS.Ident mname) args) formalParams
                     mwrapped = HS.Lambda (mkLoc p) [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs|sync' this obj' $mapplied|]
                 in [hs|(\ this'' -> $mwrapped ($(fieldFun ident) this'')) =<< I'.lift (I'.readIORef this')|]
            else let mapplied = runReader (let ?vars = localVars in foldlM
                                                    (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs|$acc <*> $targ|])
                                                    [hs|I'.pure $(HS.Var $ HS.UnQual $ HS.Ident mname)|]                                                    
                                                    args) formalParams
                     mwrapped = HS.Lambda (mkLoc p) [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs|sync' this obj' =<< I'.lift ($mapplied)|]
                 in [hs|(\ this'' -> $mwrapped ($(fieldFun ident) this'')) =<< I'.lift (I'.readIORef this')|]
      Just _ -> errorPos p "caller field not of interface type"
      Nothing -> errorPos p "no such field"
  ABS.ELit ABS.LNull -> errorPos p "null cannot be the object callee"
  _ -> errorPos p "current compiler limitation: the object callee cannot be an arbitrary pure-exp"

tEffExp (ABS.ThisSyncMethCall (ABS.L (_,mname)) args) _ = do
  (formalParams, localVars) <- getFormalLocal
  (_,fields,onlyPureDeps) <- depends args
  pure $ 
    if onlyPureDeps
    then let mapplied = runReader (let ?tyvars = [] in foldlM
                                               (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                               (maybeMangleCall mname)
                                               args) formalParams
         in maybeThisLifted fields [hs|this <..> $mapplied|]
    else let mapplied = runReader (let ?vars = localVars in foldlM
                                              (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs|$acc <*> $targ|])
                                              ((\ e-> [hs|I'.pure $e|]) (maybeMangleCall mname))
                                              args) formalParams
         in [hs|(this <..>) =<< I'.lift $(maybeThis fields mapplied)|]

tEffExp (ABS.AsyncMethCall pexp (ABS.L (p,mname)) args) isAlone = case pexp of
  ABS.ELit ABS.LThis -> do
    (formalParams, localVars) <- getFormalLocal
    (_,fields,onlyPureDeps) <- depends args
    pure $ maybeLift $ 
      if onlyPureDeps
      then let mapplied = runReader (let ?tyvars = [] in foldlM
                                                 (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                 (maybeMangleCall mname)
                                                 args) formalParams
            in maybeThis fields $ if isAlone 
                                  then [hs|(this <!!> $mapplied)|]
                                  else [hs|(this <!> $mapplied)|]
      else let mapplied = runReader (let ?vars = localVars in foldlM
                                              (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs|$acc <*> $targ|])
                                              ((\ e-> [hs|I'.pure $e|]) (maybeMangleCall mname))
                                              args) formalParams
           in if isAlone 
              then [hs|(this <!!>) =<< $(maybeThis fields mapplied)|]
              else [hs|(this <!>) =<< $(maybeThis fields mapplied)|]
  ABS.EVar ident@(ABS.L (_,calleeVar)) -> do
    (formalParams, localVars) <- getFormalLocal
    scopeLevels <- get
    case M.lookup ident (M.unions scopeLevels) of -- check type in the scopes
      Just (ABS.TSimple qtyp) -> do -- only interface type allowed
          (_,fields,onlyPureDeps) <- depends args
          let (prefix, iident) = splitQU qtyp
              iname = (if null prefix then HS.UnQual else HS.Qual $ HS.ModuleName prefix) $ HS.Ident iident
          pure $ maybeLift $ 
            if onlyPureDeps
            then let mapplied = runReader (let ?tyvars = [] in foldlM
                                                         (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                         (HS.Var $ HS.UnQual $ HS.Ident mname) args) formalParams
                     mwrapped = HS.Lambda (mkLoc p) [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] $ if isAlone
                                                                                               then [hs|(obj' <!!> $mapplied)|] -- optimized, fire&forget
                                                                                               else [hs|(obj' <!> $mapplied)|]
                 in if ident `M.member` formalParams
                    then [hs|($(maybeThis fields mwrapped)) $(HS.Var $ HS.UnQual $ HS.Ident calleeVar)|]
                    else [hs|($(maybeThis fields mwrapped)) =<< (I'.readIORef $(HS.Var $ HS.UnQual $ HS.Ident calleeVar))|]
            else let mapplied = runReader (let ?vars = localVars in foldlM
                                                    (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs|$acc <*> $targ|])
                                                    [hs|I'.pure $(HS.Var $ HS.UnQual $ HS.Ident mname)|]                                                    
                                                    args) formalParams
                     mwrapped = HS.Lambda (mkLoc p) [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] $ if isAlone
                                                                                                 then [hs|(obj' <!!>) =<< $mapplied|]
                                                                                                 else [hs|(obj' <!>) =<< $mapplied|]
                 in if ident `M.member` formalParams
                    then [hs|($(maybeThis fields mwrapped)) $(HS.Var $ HS.UnQual $ HS.Ident calleeVar)|]
                    else [hs|($(maybeThis fields mwrapped)) =<< (I'.readIORef $(HS.Var $ HS.UnQual $ HS.Ident calleeVar))|]
      Just _ ->  errorPos p "caller variable not of interface type"
      Nothing -> if ident `M.member` ?fields
                then tEffExp (ABS.AsyncMethCall (ABS.EField ident) (ABS.L (p,mname)) args) isAlone -- rewrite it to this.var
                else errorPos p "cannot find variable"
  ABS.EField ident ->
    case M.lookup ident ?fields of
      Just (ABS.TSimple qtyp) -> do -- only interface type
          (formalParams, localVars) <- getFormalLocal
          (_,_,onlyPureDeps) <- depends args
          let (prefix, iident) = splitQU qtyp
              iname = (if null prefix then HS.UnQual else HS.Qual $ HS.ModuleName prefix) $ HS.Ident iident
          pure $ maybeLift $ 
            if onlyPureDeps
            then let mapplied = runReader (let ?tyvars = [] in foldlM
                                                         (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                         (HS.Var $ HS.UnQual $ HS.Ident mname) args) formalParams
                     mwrapped = HS.Lambda (mkLoc p) [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] $ if isAlone
                                                                                                  then [hs|(obj' <!!> $mapplied)|]
                                                                                                  else [hs|(obj' <!> $mapplied)|]
                 in [hs|(\ this'' -> $mwrapped ($(fieldFun ident) this'')) =<< I'.readIORef this'|]
            else let mapplied = runReader (let ?vars = localVars in foldlM
                                                    (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs|$acc <*> $targ|])
                                                    [hs|I'.pure $(HS.Var $ HS.UnQual $ HS.Ident mname)|]                                                    
                                                    args) formalParams
                     mwrapped = HS.Lambda (mkLoc p) [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] $ if isAlone
                                                                                                  then [hs|(obj' <!!>) =<< $mapplied|]
                                                                                                  else [hs|(obj' <!>) =<< $mapplied|]
                 in [hs|(\ this'' -> $mwrapped ($(fieldFun ident) this'')) =<< I'.readIORef this'|]
      Just _ -> errorPos p "caller field not of interface type"
      Nothing -> errorPos p "no such field"
  ABS.ELit ABS.LNull -> errorPos p "null cannot be the object callee"
  _ -> errorPos p "current compiler limitation: the object callee cannot be an arbitrary pure-exp"
  

tEffExp (ABS.AwaitMethCall pexp (ABS.L (p,mname)) args) _isAlone = case pexp of
  ABS.ELit ABS.LThis -> do
          (formalParams, localVars) <- getFormalLocal
          (_,fields,onlyPureDeps) <- depends args
          pure $
            if onlyPureDeps
            then let mapplied = runReader (let ?tyvars = [] in foldlM
                                                         (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                         (maybeMangleCall mname)
                                                         args) formalParams
                 in maybeThisLifted fields [hs|awaitSugar' this (\ _ -> I'.pure ()) this ($mapplied)|]
            else let mapplied = runReader (let ?vars = localVars in foldlM
                                                    (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs|$acc <*> $targ|])
                                                    ((\ e-> [hs|I'.pure $e|]) (maybeMangleCall mname))
                                                    args) formalParams
                     
                 in [hs|awaitSugar' this (\ _ -> I'.pure ()) this =<< I'.lift $(maybeThis fields mapplied)|]
  ABS.EVar ident@(ABS.L (_,calleeVar)) -> do
    (formalParams, localVars) <- getFormalLocal
    scopeLevels <- get
    case M.lookup ident (M.unions scopeLevels) of -- check type in the scopes
      Just (ABS.TSimple qtyp) -> do -- only interface type
          (_,fields,onlyPureDeps) <- depends args
          let (prefix, iident) = splitQU qtyp
              iname = (if null prefix then HS.UnQual else HS.Qual $ HS.ModuleName prefix) $ HS.Ident iident
          pure $ maybeThisLifted fields $
            if onlyPureDeps
            then let mapplied = runReader (let ?tyvars = [] in foldlM
                                                         (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                         (HS.Var $ HS.UnQual $ HS.Ident mname)
                                                         args) formalParams
                     mwrapped = HS.Lambda (mkLoc p) [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs|awaitSugar' this (\ _ -> I'.pure ()) obj' $mapplied|]
                 in if ident `M.member` formalParams
                    then [hs|($mwrapped) $(HS.Var $ HS.UnQual $ HS.Ident calleeVar)|]
                    else [hs|($mwrapped) =<< I'.lift (I'.readIORef $(HS.Var $ HS.UnQual $ HS.Ident calleeVar))|]
            else let mapplied = runReader (let ?vars = localVars in foldlM
                                                    (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs|$acc <*> $targ|])
                                                    [hs|I'.pure $(HS.Var $ HS.UnQual $ HS.Ident mname)|]
                                                    args) formalParams
                     mwrapped = HS.Lambda (mkLoc p) [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs|awaitSugar' this (\ _ -> I'.pure ()) obj' =<< I'.lift ($mapplied)|]
                 in if ident `M.member` formalParams
                    then [hs|($mwrapped) $(HS.Var $ HS.UnQual $ HS.Ident calleeVar)|]
                    else [hs|($mwrapped) =<< I'.lift (I'.readIORef $(HS.Var $ HS.UnQual $ HS.Ident calleeVar))|]
      Just _ ->  errorPos p "caller variable not of interface type"
      Nothing -> if ident `M.member` ?fields
                 then tEffExp (ABS.AwaitMethCall (ABS.EField ident) (ABS.L (p,mname)) args) _isAlone -- rewrite it to this.var
                 else errorPos p "cannot find variable"
  ABS.EField ident ->
    case M.lookup ident ?fields of
      Just (ABS.TSimple qtyp) -> do -- only interface type
          (formalParams, localVars) <- getFormalLocal
          (_,_,onlyPureDeps) <- depends args
          let (prefix, iident) = splitQU qtyp
              iname = (if null prefix then HS.UnQual else HS.Qual $ HS.ModuleName prefix) $ HS.Ident iident
          pure $
            if onlyPureDeps
            then let mapplied = runReader (let ?tyvars = [] in foldlM
                                                         (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                                                         (HS.Var $ HS.UnQual $ HS.Ident mname) args) formalParams
                     mwrapped = HS.Lambda (mkLoc p) [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs|awaitSugar' this (\ _ -> I'.pure ()) obj' $mapplied|]
                 in [hs|(\ this'' -> $mwrapped ($(fieldFun ident) this'')) =<< I'.lift (I'.readIORef this')|]
            else let mapplied = runReader (let ?vars = localVars in foldlM
                                                    (\ acc nextArg -> tStmExp nextArg >>= \ targ -> pure [hs|$acc <*> $targ|])
                                                    [hs|I'.pure $(HS.Var $ HS.UnQual $ HS.Ident mname)|]                                                    
                                                    args) formalParams
                     mwrapped = HS.Lambda (mkLoc p) [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs|awaitSugar' this (\ _ -> I'.pure ()) obj' =<< I'.lift ($mapplied)|]
                 in [hs|(\ this'' -> $mwrapped ($(fieldFun ident) this'')) =<< I'.lift (I'.readIORef this')|]
      Just _ -> errorPos p "caller field not of interface type"
      Nothing -> errorPos p "no such field"
  ABS.ELit ABS.LNull -> errorPos p "null cannot be the object callee"
  _ -> errorPos p "current compiler limitation: the object callee cannot be an arbitrary pure-exp"


tEffExp (ABS.Get pexp) _ = do
  (formalParams, localVars) <- getFormalLocal
  (_,fields,onlyPureDeps) <- depends [pexp]
  let sureLift = if ?isInit then error "get not allowed inside init" else (\e -> [hs|I'.lift ($e)|])
  pure $ sureLift $
    if onlyPureDeps
    then let texp = runReader (let ?tyvars = [] in tPureExp pexp) formalParams
         in maybeThis fields [hs|get $texp|]
    else let texp = runReader (let ?vars = localVars in tStmExp pexp) formalParams
         in [hs|get =<< $(maybeThis fields texp)|]

tEffExp (ABS.ProTry pexp) _ = do
  (formalParams, localVars) <- getFormalLocal
  (_,fields,onlyPureDeps) <- depends [pexp]
  pure $ maybeLift $ 
    if onlyPureDeps
    then let texp = runReader (let ?tyvars = [] in tPureExp pexp) formalParams
         in maybeThis fields [hs|pro_try $texp|]
    else let texp = runReader (let ?vars = localVars in tStmExp pexp) formalParams
         in [hs|pro_try =<< $(maybeThis fields texp)|]


tEffExp ABS.ProNew _ = pure $ maybeLift [hs|pro_new|]
tEffExp ABS.Now _ = pure $ maybeLift [hs|now|]
tEffExp ABS.Readln _ = pure $ maybeLift [hs|readln|]


-- HELPERS
----------

addToScope :: ABS.T -> ABS.L -> BlockScope ()
addToScope typ var@(ABS.L (p,pid)) = do
  (topscope:restscopes) <- get
  if (any (\ scope -> var `M.member` scope) restscopes)
    then errorPos p $ pid ++ " already defined in an outer scope"
    else put $ M.insertWith (const $ const $ errorPos p $ pid ++ " already defined in this scope") var typ topscope  : restscopes

maybeLift :: (?isInit::Bool) => HS.Exp -> HS.Exp
maybeLift e = if ?isInit then e else [hs|I'.lift ($e)|]
maybeThis :: [ABS.L] -> HS.Exp -> HS.Exp
maybeThis fieldDeps e = if null fieldDeps then e else [hs|(\ this'' -> $e) =<< I'.readIORef this'|]
maybeThisLifted :: [ABS.L] -> HS.Exp -> HS.Exp
maybeThisLifted fieldDeps e = if null fieldDeps then e else [hs|(\ this'' -> $e) =<< I'.lift (I'.readIORef this')|]       

fieldFun :: (?cname::String) => ABS.L -> HS.Exp
fieldFun (ABS.L (_, f)) = HS.Var $ HS.UnQual $ HS.Ident $ f ++ "'" ++ ?cname

recordUpdate :: (?cname::String) => String -> HS.Exp
recordUpdate field = HS.RecUpdate [hs|this''|] [HS.FieldUpdate (HS.UnQual $ HS.Ident $ field ++ "'" ++ ?cname) [hs|v'|]]
                     

-- | if it is method call to an "alone method",its name should be mangled
maybeMangleCall :: (?cAloneMethods::[String], ?cname::String) => String -> HS.Exp
maybeMangleCall mname = HS.Var $ HS.UnQual $ HS.Ident $ if mname `elem` ?cAloneMethods then mname ++ "''" ++ ?cname else mname

getFormalLocal :: BlockScope (ScopeLVL, ScopeLVL)
getFormalLocal = do
  scopeLevels <- get
  pure ( last scopeLevels -- Formal Parameters
       , M.unions $ init scopeLevels) -- Collapsed Local Variables
      

depends :: (?fields::ScopeLVL, ?st::SymbolTable) 
        => [ABS.PureExp]
        -> BlockScope ([ABS.L], [ABS.L], Bool)
depends pexps = do
  (localsMany,fieldsMany,hasForeignsMany) <- unzip3 <$> mapM depend pexps
  pure (concat localsMany, concat fieldsMany, null (concat localsMany) && not (or hasForeignsMany)) where

 depend e = runReader (depend' e ([],[],False)) . M.unions . init <$> get
    
 depend' pexp (rlocal,rfields,hasForeigns) = do
  scope <- ask
  case pexp of
    ABS.EField ident -> pure (rlocal, ident:rfields,hasForeigns)
    ABS.EVar ident@(ABS.L (_,str)) -> pure $ if ident `M.member` scope 
                            then (ident:rlocal,rfields,hasForeigns)
                            else if ident `M.member` ?fields
                                 then (rlocal,ident:rfields,hasForeigns)
                                 else case find (\ (SN str' modul,_) -> str == str' && maybe False (not . snd) modul) (M.assocs ?st) of
                                        Just (_,SV Foreign _) ->  (rlocal, rfields,True)
                                        _ -> (rlocal, rfields,hasForeigns)
    ABS.ELet (ABS.FormalPar _ ident) pexpEq pexpIn -> do
                                    (rlocalEq, rfieldsEq,hasForeignsEq) <- depend' pexpEq ([],[],False)
                                    (rlocalIn, rfieldsIn,hasForeignsIn) <- let fields' = ?fields
                                                            in
                                                              let ?fields = M.delete ident fields' 
                                                              in local (M.delete ident) (depend' pexpIn ([],[],False))
                                    pure (rlocal++rlocalEq++rlocalIn, rfields++rfieldsEq++rfieldsIn,hasForeigns||hasForeignsEq||hasForeignsIn)
    -- ABS.ESinglConstr qtyp -> pure $ let (prefix, str) = splitQType qtyp
    --                                in case find (\ (SN str' modul,_) -> str == str' && maybe False (not . snd) modul) (M.assocs ?st) of
    --                                     Just (_,SV Foreign _) ->  (rlocal, rfields,True)
    --                                     _ -> (rlocal, rfields,hasForeigns)
    ABS.ECase pexpOf branches -> do
        (rlocalOf, rfieldsOf,hasForeignsOf) <- depend' pexpOf (rlocal,rfields,hasForeigns)      
        foldl (\ (acc1,acc2,acc3) (x1,x2,x3) -> (acc1++x1,acc2++x2,acc3||x3)) (rlocal++rlocalOf, rfields++rfieldsOf,hasForeigns||hasForeignsOf)
              <$> mapM (\ (ABS.ECaseBranch pat pexpBranch) ->
                  let fields' = ?fields
                      idents = collectPatVars pat
                      collectPatVars (ABS.PVar ident) = [ident]
                      collectPatVars (ABS.PParamConstr _ pats) = concatMap collectPatVars pats
                      collectPatVars _ = []
                  in
                    let ?fields = foldl (flip M.delete) fields' idents
                    in local (\ scope' -> foldl (flip M.delete) scope' idents) (depend' pexpBranch ([],[],False))
                  ) branches

    ABS.EOr e e' -> foldl (\ (acc1,acc2,acc3) (x1,x2,x3) -> (acc1++x1,acc2++x2,acc3||x3)) (rlocal, rfields, hasForeigns) <$> mapM (\ ex -> depend' ex ([],[],False)) [e,e']
    ABS.EAnd e e' -> foldl (\ (acc1,acc2,acc3) (x1,x2,x3) -> (acc1++x1,acc2++x2,acc3||x3)) (rlocal, rfields, hasForeigns) <$> mapM (\ ex -> depend' ex ([],[],False)) [e,e']
    ABS.EEq e e' -> foldl (\ (acc1,acc2,acc3) (x1,x2,x3) -> (acc1++x1,acc2++x2,acc3||x3)) (rlocal, rfields, hasForeigns) <$> mapM (\ ex -> depend' ex ([],[],False)) [e,e']
    ABS.ENeq e e' -> foldl (\ (acc1,acc2,acc3) (x1,x2,x3) -> (acc1++x1,acc2++x2,acc3||x3)) (rlocal, rfields, hasForeigns) <$> mapM (\ ex -> depend' ex ([],[],False)) [e,e']
    ABS.ELt e e' -> foldl (\ (acc1,acc2,acc3) (x1,x2,x3) -> (acc1++x1,acc2++x2,acc3||x3)) (rlocal, rfields, hasForeigns) <$> mapM (\ ex -> depend' ex ([],[],False)) [e,e']
    ABS.ELe e e' -> foldl (\ (acc1,acc2,acc3) (x1,x2,x3) -> (acc1++x1,acc2++x2,acc3||x3)) (rlocal, rfields, hasForeigns) <$> mapM (\ ex -> depend' ex ([],[],False)) [e,e']
    ABS.EGt e e' -> foldl (\ (acc1,acc2,acc3) (x1,x2,x3) -> (acc1++x1,acc2++x2,acc3||x3)) (rlocal, rfields, hasForeigns) <$> mapM (\ ex -> depend' ex ([],[],False)) [e,e']
    ABS.EGe e e' -> foldl (\ (acc1,acc2,acc3) (x1,x2,x3) -> (acc1++x1,acc2++x2,acc3||x3)) (rlocal, rfields, hasForeigns) <$> mapM (\ ex -> depend' ex ([],[],False)) [e,e']
    ABS.EAdd e e' -> foldl (\ (acc1,acc2,acc3) (x1,x2,x3) -> (acc1++x1,acc2++x2,acc3||x3)) (rlocal, rfields, hasForeigns) <$> mapM (\ ex -> depend' ex ([],[],False)) [e,e']
    ABS.ESub e e' -> foldl (\ (acc1,acc2,acc3) (x1,x2,x3) -> (acc1++x1,acc2++x2,acc3||x3)) (rlocal, rfields, hasForeigns) <$> mapM (\ ex -> depend' ex ([],[],False)) [e,e']
    ABS.EMul e e' -> foldl (\ (acc1,acc2,acc3) (x1,x2,x3) -> (acc1++x1,acc2++x2,acc3||x3)) (rlocal, rfields, hasForeigns) <$> mapM (\ ex -> depend' ex ([],[],False)) [e,e']
    ABS.EDiv e e' -> foldl (\ (acc1,acc2,acc3) (x1,x2,x3) -> (acc1++x1,acc2++x2,acc3||x3)) (rlocal, rfields, hasForeigns) <$> mapM (\ ex -> depend' ex ([],[],False)) [e,e']
    ABS.EMod e e' -> foldl (\ (acc1,acc2,acc3) (x1,x2,x3) -> (acc1++x1,acc2++x2,acc3||x3)) (rlocal, rfields, hasForeigns) <$> mapM (\ ex -> depend' ex ([],[],False)) [e,e']
    ABS.ELogNeg e -> depend' e (rlocal, rfields, hasForeigns)
    ABS.EIntNeg e -> depend' e (rlocal, rfields, hasForeigns)
    ABS.EFunCall (ABS.L_ (ABS.L (_,str))) es -> foldl (\ (acc1,acc2,acc3) (x1,x2,x3) -> (acc1++x1,acc2++x2,acc3||x3)) 
              (case find (\ (SN str' modul,_) -> str == str' && maybe False (not . snd) modul) (M.assocs ?st) of
                 Just (_,SV Foreign _) ->  (rlocal, rfields,True)
                 _ -> (rlocal, rfields,hasForeigns)) <$> mapM (\ ex -> depend' ex ([],[],False)) es
    ABS.ENaryFunCall (ABS.L_ (ABS.L (_,str))) es -> foldl (\ (acc1,acc2,acc3) (x1,x2,x3) -> (acc1++x1,acc2++x2,acc3||x3)) 
              (case find (\ (SN str' modul,_) -> str == str' && maybe False (not . snd) modul) (M.assocs ?st) of
                 Just (_,SV Foreign _) ->  (rlocal, rfields,True)
                 _ -> (rlocal, rfields,hasForeigns)) <$> mapM (\ ex -> depend' ex ([],[],False)) es
    ABS.EParamConstr _qtyp es -> foldl (\ (acc1,acc2,acc3) (x1,x2,x3) -> (acc1++x1,acc2++x2,acc3||x3)) (rlocal, rfields,hasForeigns) <$> mapM (\ ex -> depend' ex ([],[],False)) es
    ABS.EIf e e' e'' -> foldl (\ (acc1,acc2,acc3) (x1,x2,x3) -> (acc1++x1,acc2++x2,acc3||x3)) (rlocal, rfields,hasForeigns) <$>  mapM (\ ex -> depend' ex ([],[],False)) [e,e',e'']
    _ -> return (rlocal, rfields, hasForeigns)


