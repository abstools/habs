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

tMethod :: (?st :: SymbolTable) => 
          ABS.Block                 -- the method body
        -> [ABS.Param]               -- the method params
        -> M.Map ABS.LIdent ABS.Type -- the fields
        -> HS.Exp
tMethod (ABS.Bloc astms) params fields = evalState (let ?fields = fields 
                                                     in HS.Do . concat <$> mapM tStm astms) -- fixed fields passed as an implicit param
                                         [M.fromList (map (\ (ABS.Par t i) -> (i,t)) params)] -- first scope level is the formal params

tStm (ABS.AnnStm _ (ABS.SDec t i@(ABS.LIdent (p,n)))) =  case t of

  ABS.TGen (ABS.QTyp [ABS.QTypeSegmen (ABS.UIdent (_,"Fut"))])  _ -> do   -- it is an unitialized future (set to newEmptyMVar)
      addToScope t i
      pure [HS.Generator noLoc 
                   (HS.PatTypeSig noLoc (HS.PVar $ HS.Ident n) (tType t))   -- f :: IORef (Fut a) <- emptyFuture
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
                                                      (HS.PatTypeSig noLoc (HS.PVar $ HS.Ident n) (tType t)) -- o :: IORef Interf <- null
                                                      [hs| newIORef null |] ]
                          Foreign -> do
                            addToScope t i
                            pure [HS.Generator noLoc
                                        (HS.PVar $ HS.Ident n) -- no type of foreign object :  foreign <- newIORef undefined
                                        [hs| newIORef undefined |] ]
                          _ -> errorPos p "A field must be initialised if it is not of a reference type"


tStm (ABS.AnnStm _ (ABS.SDecAss t i@(ABS.LIdent (_,n)) e)) = do
  addToScope t i
  pure [ HS.Generator noLoc (HS.PatTypeSig noLoc (HS.PVar $ HS.Ident n) (tType t)) [hs| null |] ]

tStm (ABS.AnnStm _ (ABS.SAss i e)) = undefined

tStm (ABS.AnnStm _ (ABS.SFieldAss i e)) = undefined

tStm (ABS.AnnStm _ (ABS.SSkip)) = pure []

tStm (ABS.AnnStm _ ABS.SSuspend) = pure [HS.Qualifier [hs| suspend this |]]

tStm (ABS.AnnStm a (ABS.SReturn e)) = tStm (ABS.AnnStm a (ABS.SExp e))

tStm (ABS.AnnStm _ (ABS.SThrow pexp)) = do
  texp <- tPureExpLifted pexp
  pure [HS.Qualifier [hs| throw $texp |]]

tStm (ABS.AnnStm _ (ABS.SIf pexp stmThen)) = do
  texp <- tPureExpLifted pexp
  [HS.Qualifier tthen] <- tStm $ ABS.AnnStm [] (ABS.SBlock [stmThen])
  pure [ HS.Generator noLoc (HS.PVar $ HS.Ident "when'") texp
       , HS.Qualifier $ [hs| when if' $tthen |] ]

tStm (ABS.AnnStm _ (ABS.SIfElse pexp stmThen stmElse)) = do
  texp <- tPureExpLifted pexp
  [HS.Qualifier tthen] <- tStm $ ABS.AnnStm [] (ABS.SBlock [stmThen])
  [HS.Qualifier telse] <- tStm $ ABS.AnnStm [] (ABS.SBlock [stmElse])
  pure [ HS.Generator noLoc (HS.PVar $ HS.Ident "if'") texp
       , HS.Qualifier $ [hs| if if' then $tthen else $telse |] ]


tStm (ABS.AnnStm _ (ABS.SBlock astms)) = do
  modify' (M.empty:)            -- add level
  tstms <- mapM tStm astms
  modify' tail                  -- remove level
  pure [HS.Qualifier $ HS.Do $ concat tstms]

-- helpers

tPureExpLifted pexp = do
  stmScope <- get
  pure $ runReader (let ?tyvars = [] in tPureExp pexp) (M.unions stmScope)

addToScope :: ABS.Type -> ABS.LIdent -> StmScope ()
addToScope typ var@(ABS.LIdent (p,pid)) = do
  (topscope:restscopes) <- get
  if (any (\ scope -> var `M.member` scope) restscopes)
    then errorPos p $ pid ++ " already defined in an outer scope"
    else put $ M.insertWith (const $ const $ errorPos p $ pid ++ " already defined in this scope") var typ topscope  : restscopes
