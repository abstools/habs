{-# LANGUAGE ImplicitParams #-}
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
    ) where

import qualified ABS.AST as ABS
import Language.Haskell.Exts.SrcLoc (SrcLoc (..))

import Data.Char (toLower)
import Debug.Trace (trace)

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