{-# LANGUAGE CPP, ImplicitParams #-}
module ABS.Compiler.Codegen.Pat 
    ( tPattern
    ) where

import ABS.Compiler.Codegen.Base
import ABS.Compiler.Utils
import qualified ABS.AST as ABS
import qualified Language.Haskell.Exts as HS
import Data.Map (member)
import Control.Monad.Trans.Reader (ask)


import Control.Exception (assert)
#define todo assert False


-- | Translating a pattern of an ABS case-branch in pure case-pattern-matching
tPattern :: (?fields::ScopeLVL) => ABS.Pattern -> LetScope (HS.Pat, [HS.Stmt])
tPattern (ABS.PVar i@(ABS.L (_,pid))) = do
  scope <- ask
  pure $ if i `member` scope || i `member` ?fields
         then (HS.PVar $ HS.Ident $ pid ++ "'", [HS.Qualifier $ HS.InfixApp (HS.Var $ HS.UnQual $ HS.Ident $ pid ++ "'")
                                                                            (HS.QVarOp $ HS.UnQual $ HS.Symbol "==")
                                                                            (HS.Var $ HS.UnQual $ HS.Ident pid)])
         else (HS.PVar $ HS.Ident $ pid, [])
tPattern (ABS.PSinglConstr (ABS.U_ (ABS.U (_,"Nil")))) = pure (HS.PList [], [])
tPattern (ABS.PSinglConstr (ABS.U_ (ABS.U (_,"Unit")))) = pure (HS.PTuple HS.Boxed [], []) -- () unit constructor
tPattern (ABS.PSinglConstr (ABS.U_ (ABS.U (_, tid)))) = pure (HS.PApp (HS.UnQual $ HS.Ident tid) [] , [])
tPattern (ABS.PParamConstr (ABS.U_ (ABS.U (p,"Triple"))) subpats) | length subpats == 3 = do
  (tpats,tguards) <- unzip <$> mapM tPattern subpats
  pure (HS.PTuple HS.Boxed tpats, concat tguards)
                                                               | otherwise = errorPos p "wrong number of arguments to Triple"
tPattern (ABS.PParamConstr (ABS.U_ (ABS.U (p,"Pair"))) subpats) | length subpats == 2 = do
  (tpats,tguards) <- unzip <$> mapM tPattern subpats
  pure (HS.PTuple HS.Boxed tpats, concat tguards)
                                                             | otherwise = errorPos p "wrong number of arguments to Pair"
tPattern (ABS.PParamConstr (ABS.U_ (ABS.U (_,"Cons"))) [subpat1, subpat2]) = do
  (tpat1,tguard1) <- tPattern subpat1
  (tpat2,tguard2) <- tPattern subpat2
  pure (HS.PParen $ HS.PInfixApp tpat1 (HS.Special $ HS.Cons) tpat2, tguard1++tguard2)
tPattern (ABS.PParamConstr (ABS.U_ (ABS.U (p,"Cons"))) _) = errorPos p "wrong number of arguments to Cons"
tPattern (ABS.PParamConstr (ABS.U_ (ABS.U (p,"InsertAssoc"))) _) = errorPos p "InsertAssoc is unsafe, you should avoid it."
tPattern (ABS.PParamConstr (ABS.U_ (ABS.U (_,tid))) subpats) = do
  (tpats,tguards) <- unzip <$> mapM tPattern subpats
  pure (HS.PApp (HS.UnQual $ HS.Ident tid) tpats, concat tguards)
tPattern ABS.PWildCard = pure (HS.PWildCard, [])
tPattern (ABS.PLit lit) = pure $ (HS.PLit HS.Signless $ case lit of
                                         (ABS.LStr str) ->  HS.String str
                                         (ABS.LInt i) ->  HS.Int i
                                         _ -> error "this or null are not allowed in pattern syntax"
                                  ,[])
tPattern _ = todo (error "no translation of patterns with qualified constructors")