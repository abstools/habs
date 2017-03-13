{-# LANGUAGE CPP, QuasiQuotes, ImplicitParams #-}
module ABS.Compiler.Utils 
    ( appendL
    , showQL
    , showQU
    , splitQU
    , lineQU
    , showQA
    , splitQA
    , lineQA
    , headToLower
    , errorPos, warnPos, showPos
    , noLoc', mkLoc, mkLocFromQU, mkLocFromQA
    , buildInfo, putUp
    ) where

import qualified ABS.AST as ABS
import ABS.Compiler.Firstpass.Base
import Language.Haskell.Exts.QQ (hs)
import Language.Haskell.Exts.SrcLoc (SrcLoc (..))
import qualified Language.Haskell.Exts.Syntax as HS
import qualified Data.Map as M
import Data.List (find)

import Data.Char (toLower)
import Debug.Trace (trace)

import Control.Exception (assert)
#define todo assert False (error "not implemented yet")

appendL :: ABS.L -> String -> ABS.L
appendL (ABS.L (p,s)) s' = ABS.L (p,s++s') 

showQL :: ABS.QL -> String
showQL (ABS.L_ (ABS.L (_,ident))) = ident
showQL (ABS.QL (ABS.U (_,ident)) rest) = ident ++ "." ++ showQL rest

showQU :: ABS.QU -> String
showQU (ABS.U_ (ABS.U (_,ident))) = ident
showQU (ABS.QU (ABS.U (_,ident)) rest) = ident ++ "." ++ showQU rest

splitQU :: ABS.QU -> (String, String)
splitQU (ABS.U_ (ABS.U (_,ident))) = ("", ident)
splitQU (ABS.QU (ABS.U (_,qualIdent)) rest) = let (qualRest, ident) = splitQU rest
                                          in (qualIdent ++ "." ++ qualRest, ident)

lineQU :: ABS.QU -> Int
lineQU (ABS.U_ (ABS.U ((l,_),_))) = l
lineQU (ABS.QU (ABS.U ((l,_),_)) _) = l

showQA :: ABS.QA -> String
showQA (ABS.UA (ABS.U (_,ident))) = ident
showQA (ABS.LA (ABS.L (_,ident))) = ident
showQA (ABS.QA (ABS.U (_,ident)) rest) = ident ++ "." ++ showQA rest


splitQA :: ABS.QA -> (String, String)
splitQA (ABS.UA (ABS.U (_,ident))) = ("", ident)
splitQA (ABS.LA (ABS.L (_,ident))) = ("", ident)
splitQA (ABS.QA (ABS.U (_,qualIdent)) rest) = let (qualRest, ident) = splitQA rest
                                              in (qualIdent ++ "." ++ qualRest, ident)


lineQA :: ABS.QA -> Int
lineQA (ABS.UA (ABS.U ((l,_),_))) = l
lineQA (ABS.LA (ABS.L ((l,_),_))) = l
lineQA (ABS.QA (ABS.U ((l,_),_)) _) = l



-- | Used for turning an ABS type variable (e.g. A,B,DgFx) to HS type variable (a,b,dgFx)
headToLower :: String -> String
headToLower (x:xs) = toLower x : xs
headToLower _ = error "headToLower: emptyList"

-- | Querying a statement AST
--

errorPos :: (Int, Int) -> String -> a
errorPos pos msg = error ("[error #" ++ showPos pos ++ "]" ++  msg)

warnPos :: (Int,Int) -> String -> a -> a
warnPos  pos msg = trace ("[warning #" ++ showPos pos ++ "]" ++  msg)

showPos :: (Int, Int) -> String
showPos (row,col) = show row ++ ":" ++ show col

-- | Empty source-location. Use instead of 'noLoc' which has problem when pretty-printing with LINE pragmas enabled.
noLoc' :: SrcLoc
noLoc' = SrcLoc "<unknown>.hs" 1 1

mkLocFromQU :: (?absFileName::String) => ABS.QU -> SrcLoc
mkLocFromQU qu = SrcLoc ?absFileName (lineQU qu) 1

mkLocFromQA :: (?absFileName::String) => ABS.QA -> SrcLoc
mkLocFromQA qa = SrcLoc ?absFileName (lineQA qa) 1

-- | from BNFC tokens' position
mkLoc :: (?absFileName::String) => (Int,Int) -> SrcLoc
mkLoc (line,column) = SrcLoc ?absFileName line column



-- Used for subtyping

data Info = Up
          | Deep String Int [(Int,Info)]

buildInfo :: (?st :: SymbolTable) => ABS.T -> Maybe Info
buildInfo ABS.TInfer = todo
buildInfo (ABS.TPoly (ABS.U_ (ABS.U (_,"Fut"))) _) = Nothing -- TODO: Fut<A> should be covariant, but for implementation reasons (MVar a) it is invariant
buildInfo (ABS.TPoly qu ts) = let (l, buildArgs) = foldl (\ (i,acc) t -> maybe (i+1,acc) (\x -> (i+1,(i,x):acc)) (buildInfo t) ) (0,[]) ts
                              in if null buildArgs
                                 then Nothing
                                 else Just $ Deep (showQU qu) l buildArgs
buildInfo t@(ABS.TSimple _) = if isInterface t
                              then Just Up
                              else Nothing
  where
    isInterface :: (?st::SymbolTable) => ABS.T -> Bool
    isInterface t = let
                  qtyp = case t of
                           ABS.TSimple qtyp' -> qtyp'
                           ABS.TPoly qtyp' _ -> qtyp'
                           ABS.TInfer -> todo
                  (prefix, ident) = splitQU qtyp
                  mSymbolType = if null prefix
                                then snd <$> find (\ (SN ident' modul,_) -> ident == ident' && maybe True (not . snd) modul) (M.assocs ?st)
                                else M.lookup (SN ident (Just (prefix, True))) ?st 
                in case mSymbolType of
                     Just (SV (Interface _ _) _) -> True
                     _ -> False



putUp :: Info -> HS.Exp
putUp Up = [hs|up'|]
putUp (Deep functorName functorWidth deeps) = foldl 
                                              (\ acc i -> HS.App acc $ maybe [hs|I'.id|] (HS.Paren . putUp) (lookup i deeps))
                                              (HS.Var $ HS.UnQual $ HS.Ident $ "fmap'" ++ functorName)
                                              [0..functorWidth-1]
