module ABS.Compiler.Codegen.Pat 
    ( tPattern
    ) where

import ABS.Compiler.Utils
import qualified ABS.AST as ABS
import qualified Language.Haskell.Exts as HS

-- | Translating a pattern of an ABS case-branch in pure case-pattern-matching
tPattern :: ABS.Pattern -> HS.Pat
tPattern (ABS.PIdent (ABS.LIdent (_,pid))) = HS.PVar $ HS.Ident $ pid
tPattern (ABS.PSinglConstr (ABS.UIdent (_,"Nil"))) = HS.PList []
tPattern (ABS.PSinglConstr (ABS.UIdent (_,"Unit"))) = HS.PTuple HS.Boxed [] -- () unit constructor
tPattern (ABS.PSinglConstr (ABS.UIdent (_, tid))) = HS.PApp (HS.UnQual $ HS.Ident tid) []
tPattern (ABS.PParamConstr (ABS.UIdent (p,"Triple")) subpats) | length subpats == 3 = HS.PTuple HS.Boxed (map tPattern subpats)
                                                               | otherwise = errorPos p "wrong number of arguments to Triple"
tPattern (ABS.PParamConstr (ABS.UIdent (p,"Pair")) subpats) | length subpats == 2 = HS.PTuple HS.Boxed (map tPattern subpats)
                                                             | otherwise = errorPos p "wrong number of arguments to Pair"
tPattern (ABS.PParamConstr (ABS.UIdent (_,"Cons")) [subpat1, subpat2]) = HS.PParen (HS.PInfixApp 
                                                                          (tPattern subpat1)
                                                                          (HS.Special $ HS.Cons)
                                                                          (tPattern subpat2))
tPattern (ABS.PParamConstr (ABS.UIdent (p,"Cons")) _) = errorPos p "wrong number of arguments to Cons"
tPattern (ABS.PParamConstr (ABS.UIdent (p,"InsertAssoc")) _) = errorPos p "InsertAssoc is unsafe, you should avoid it."
tPattern (ABS.PParamConstr (ABS.UIdent (_,tid)) subpats) = HS.PApp (HS.UnQual $ HS.Ident tid) (map tPattern subpats)
tPattern ABS.PUnderscore = HS.PWildCard
tPattern (ABS.PLit lit) = HS.PLit HS.Signless $ case lit of
                                         (ABS.LStr str) ->  HS.String str
                                         (ABS.LInt i) ->  HS.Int i
                                         _ -> error "this or null are not allowed in pattern syntax"
