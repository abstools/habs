{-# LANGUAGE ImplicitParams, QuasiQuotes #-}
module ABS.Compiler.Codegen.Stm
    ( tMethod
    ) where

import ABS.Compiler.Utils
import ABS.Compiler.Codegen.Base
import ABS.Compiler.Firstpass.Base
import ABS.Compiler.Codegen.Exp (tPureExp)
import ABS.Compiler.Codegen.Typ
import qualified ABS.AST as ABS
import qualified Language.Haskell.Exts.Syntax as HS
import Language.Haskell.Exts.SrcLoc (noLoc)
import Language.Haskell.Exts.QQ (hs)

import Control.Monad.Trans.State (evalState, get, put, modify')
import Control.Monad.Trans.Reader (runReader)
import qualified Data.Map as M
import Control.Applicative ((<|>))
import Data.Foldable (foldlM)

tMethod :: (?st :: SymbolTable) => ABS.Block -> [ABS.Param] -> M.Map ABS.LIdent ABS.Type -> String -> HS.Exp
tMethod (ABS.Bloc mbody) mparams fields cname = evalState (let ?fields = fields  -- fixed fields passed as an implicit param
                                                               ?cname = cname    -- className needed for field pattern-matching
                                                             in HS.Do . concat <$> mapM tStm mbody)
                                          [M.fromList (map (\ (ABS.Par t i) -> (i,t)) mparams)] -- first scope level is the formal params


--- VARIABLE-ASSIGNMENT STATEMENTS
-------------------------

tStm (ABS.AnnStm _ (ABS.SDec t i@(ABS.LIdent (p,n)))) = case t of

  ABS.TGen (ABS.QTyp [ABS.QTypeSegmen (ABS.UIdent (_,"Fut"))])  _ -> do   -- it is an unitialized future (set to newEmptyMVar)
      addToScope t i
      pure [HS.Generator noLoc 
                   (HS.PatTypeSig noLoc (HS.PVar $ HS.Ident n) (HS.TyApp (HS.TyCon $ HS.UnQual $ HS.Ident "IORef") (tType t)))   -- f :: IORef (Fut a) <- emptyFuture
                   [hs| newIORef =<< emptyFuture |]]

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
                                                      (HS.PatTypeSig noLoc (HS.PVar $ HS.Ident n) (HS.TyApp (HS.TyCon $ HS.UnQual $ HS.Ident "IORef") (tType t))) -- o :: IORef Interf <- null
                                                      [hs| newIORef null |] ]
                          Foreign -> do
                            addToScope t i
                            pure [HS.Generator noLoc
                                        (HS.PVar $ HS.Ident n) -- no type of foreign object :  foreign <- newIORef undefined
                                        [hs| newIORef undefined |] ]
                          _ -> errorPos p "A field must be initialised if it is not of a reference type"


tStm (ABS.AnnStm _ (ABS.SDecAss t i@(ABS.LIdent (_,n)) e)) = do
  addToScope t i
  pure [ HS.Generator noLoc 
               (HS.PatTypeSig noLoc (HS.PVar $ HS.Ident n) (HS.TyApp (HS.TyCon $ HS.UnQual $ HS.Ident "IORef") (tType t))) 
               [hs| newIORef |] ]

tStm (ABS.AnnStm _ (ABS.SAss i e)) = undefined

tStm (ABS.AnnStm _ (ABS.SFieldAss i e)) = undefined

-- CONCURRENCY STATEMENTS
-------------------------

tStm (ABS.AnnStm _ ABS.SSuspend) = pure [HS.Qualifier [hs| suspend this |]]

-- decompose await (g1 && g2) to await g1; await g2
tStm (ABS.AnnStm a (ABS.SAwait (ABS.AndGuard ag1 ag2))) = 
  (++) <$> tStm (ABS.AnnStm a (ABS.SAwait ag1)) <*> tStm (ABS.AnnStm a (ABS.SAwait ag2))

tStm (ABS.AnnStm _ (ABS.SAwait (ABS.FutGuard (ABS.LIdent (_, fname))))) = do
  -- TODO: check if it is in scope
  pure [HS.Qualifier [hs| awaitFuture' =<< $(HS.Var $ HS.UnQual $ HS.Ident fname) |]]

-- currently, no solution to the cosimo problem
tStm (ABS.AnnStm _ (ABS.SAwait (ABS.FutFieldGuard (ABS.LIdent (_, fname))))) = do
  let fieldFun = HS.Var $ HS.UnQual $ HS.Ident $ fname ++ "'" ++ ?cname
  pure [HS.Qualifier [hs| awaitFuture' . $fieldFun =<< readIORef this |]]

-- note to self: await b1&&b2 maybe not equal with await b1&b2;
tStm (ABS.AnnStm _ (ABS.SAwait (ABS.ExpGuard pexp))) = do
  pure [HS.Qualifier [hs| awaitBool' TODO |]]

-- CONTROL FLOW STATEMENTS
--------------------------

tStm (ABS.AnnStm _ (ABS.SWhile pexp stmBody)) = do
  texp <- liftPure $ let ?tyvars = [] in tPureExp pexp
  [HS.Qualifier tbody] <- tStm $ ABS.AnnStm [] (ABS.SBlock [stmBody])
  pure [HS.Qualifier [hs| while $texp $tbody |] ]              

tStm (ABS.AnnStm _ (ABS.SIf pexp stmThen)) = do
  texp <- liftPure $ let ?tyvars = [] in tPureExp pexp
  [HS.Qualifier tthen] <- tStm $ ABS.AnnStm [] (ABS.SBlock [stmThen])
  pure [ HS.Generator noLoc (HS.PVar $ HS.Ident "when'") texp
       , HS.Qualifier $ [hs| when if' $tthen |] ]

tStm (ABS.AnnStm _ (ABS.SIfElse pexp stmThen stmElse)) = do
  texp <- liftPure $ let ?tyvars = [] in tPureExp pexp
  [HS.Qualifier tthen] <- tStm $ ABS.AnnStm [] (ABS.SBlock [stmThen])
  [HS.Qualifier telse] <- tStm $ ABS.AnnStm [] (ABS.SBlock [stmElse])
  pure [ HS.Generator noLoc (HS.PVar $ HS.Ident "if'") texp
       , HS.Qualifier $ [hs| if if' then $tthen else $telse |] ]

-- CLASSIC IMPERATIVE STATEMENTS
--------------------------------

tStm (ABS.AnnStm _ (ABS.SBlock astms)) = do
  modify' (M.empty:)            -- add level
  tstms <- mapM tStm astms
  modify' tail                  -- remove level
  pure [HS.Qualifier $ HS.Do $ concat tstms]

tStm (ABS.AnnStm a (ABS.SReturn e)) = tStm (ABS.AnnStm a (ABS.SExp e))

tStm (ABS.AnnStm _ (ABS.SPrint pexp)) = do
  texp <- liftPure $ let ?tyvars = [] in tPureExp pexp
  pure [HS.Qualifier [hs| println $texp |]]

tStm (ABS.AnnStm _ (ABS.SSkip)) = pure []

-- expression as a standalone statement (i.e. ignoring its return result)
tStm (ABS.AnnStm _ (ABS.SExp e)) = do
  texp <- tExp e
  pure [HS.Qualifier texp]      -- todo: pass a standalone flag here

-- EXCEPTION STATEMENTS
-------------------------

tStm (ABS.AnnStm _ (ABS.SAssert pexp)) = do
  texp <- liftPure (let ?tyvars = [] in tPureExp pexp)
  pure [HS.Qualifier [hs| assert =<< $texp |] ]

tStm (ABS.AnnStm _ (ABS.SThrow pexp)) = do
  texp <- liftPure $ let ?tyvars = [] in tPureExp pexp
  pure [HS.Qualifier [hs| throw $texp |]]

tStm (ABS.AnnStm _ (ABS.STryCatchFinally try_stm cbranches mfinally)) = undefined


-- (EFFECTFUL) EXPRESSIONS in statement world
---------------------------------------------

-- | lifting pure expressions into statement world

tExp (ABS.ExpP pexp) = liftPure (let ?tyvars = [] in tPureExp pexp)
tExp (ABS.ExpE eexp) = tEffExp eexp

tEffExp (ABS.New qcname args) = do
      let (q, cname) = splitQType qcname
          smartCon = HS.Var $ (if null q then HS.UnQual else HS.Qual $ HS.ModuleName q) $ HS.Ident $ "smart'" ++ cname
          initFun = HS.Var $ (if null q then HS.UnQual else HS.Qual $ HS.ModuleName q) $ HS.Ident $ "init'" ++ cname
      initApplied <- liftPure $ let ?tyvars = [] in foldlM
                    (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                    initFun
                    args
      pure [hs| new $smartCon $initApplied |]

tEffExp (ABS.NewLocal qcname args) = do
      let (q, cname) = splitQType qcname
          smartCon = HS.Var $ (if null q then HS.UnQual else HS.Qual $ HS.ModuleName q) $ HS.Ident $ "smart'" ++ cname
          initFun = HS.Var $ (if null q then HS.UnQual else HS.Qual $ HS.ModuleName q) $ HS.Ident $ "init'" ++ cname
      initApplied <- liftPure $ let ?tyvars = [] in foldlM
                    (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                    initFun
                    args
      pure [hs| new $smartCon $initApplied this |]

-- limits: PVar, this, null can be compiled
-- other general pexps is limitation
tEffExp (ABS.SyncMethCall pexp (ABS.LIdent (p,mname)) args) = case pexp of
  ABS.EVar ident -> do
    typ <- M.lookup ident . M.unions <$> get -- check type in the scopes
    case typ of
      Just (ABS.TSimple qtyp) -> do -- only interface type
          mapplied <- liftPure $ let ?tyvars = [] in foldlM
                     (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                     (HS.Var $ HS.UnQual $ HS.Ident mname)
                     args
          let (prefix, iident) = splitQType qtyp
              iname = (if null prefix then HS.UnQual else HS.Qual $ HS.ModuleName prefix) $ HS.Ident iident
          pure $ HS.Lambda noLoc [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs| obj' <.> $mapplied |]
      Nothing -> errorPos p "cannot find variable"
      _ -> errorPos p "invalid object callee type"
  ABS.ELit ABS.LNull -> errorPos p "null cannot be the object callee"
  _ -> errorPos p "current compiler limitation: the object callee cannot be an arbitrary pure-exp"

tEffExp (ABS.ThisSyncMethCall (ABS.LIdent (_,mname)) args) = do
  mapplied <- liftPure $ let ?tyvars = [] in foldlM
             (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
             (HS.Var $ HS.UnQual $ HS.Ident mname)
             args
  pure [hs| this <..> $mapplied |]

-- limits: PVar, this, null can be compiled
-- other general pexps is limitation
tEffExp (ABS.AsyncMethCall pexp (ABS.LIdent (p,mname)) args) = case pexp of
  ABS.EVar ident -> do
    typ <- M.lookup ident . M.unions <$> get -- check type in the scopes
    case typ of
      Just (ABS.TSimple qtyp) -> do -- only interface type
          mapplied <- liftPure $ let ?tyvars = [] in foldlM
                     (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
                     (HS.Var $ HS.UnQual $ HS.Ident mname)
                     args
          let (prefix, iident) = splitQType qtyp
              iname = (if null prefix then HS.UnQual else HS.Qual $ HS.ModuleName prefix) $ HS.Ident iident
          pure $ HS.Lambda noLoc [HS.PApp iname [HS.PVar $ HS.Ident "obj'"]] [hs| obj' <!> $mapplied |]
      Nothing -> errorPos p "cannot find variable"
      _ -> errorPos p "invalid object callee type"
  ABS.ELit ABS.LNull -> errorPos p "null cannot be the object callee"
  _ -> errorPos p "current compiler limitation: the object callee cannot be an arbitrary pure-exp"
  
tEffExp (ABS.ThisAsyncMethCall (ABS.LIdent (_,mname)) args) = do
  mapplied <- liftPure $ let ?tyvars = [] in foldlM
             (\ acc nextArg -> HS.App acc <$> tPureExp nextArg)
             (HS.Var $ HS.UnQual $ HS.Ident mname)
             args
  pure [hs| this <!> $mapplied |]

-- TODO: osync optimization

tEffExp (ABS.Get pexp) = do
  texp <- liftPure (let ?tyvars = [] in tPureExp pexp)
  pure [hs| get =<< $texp |] 


-- HELPERS
----------

addToScope :: ABS.Type -> ABS.LIdent -> StmScope ()
addToScope typ var@(ABS.LIdent (p,pid)) = do
  (topscope:restscopes) <- get
  if (any (\ scope -> var `M.member` scope) restscopes)
    then errorPos p $ pid ++ " already defined in an outer scope"
    else put $ M.insertWith (const $ const $ errorPos p $ pid ++ " already defined in this scope") var typ topscope  : restscopes


-- | lifting pure expressions into statement world
liftPure :: (?st :: SymbolTable, ?fields :: M.Map ABS.LIdent ABS.Type, ?cname :: String)
           => ExpScope HS.Exp -> StmScope HS.Exp
liftPure pexp = do
  stmScope <- get
  pure $ runReader pexp (M.unions stmScope)
