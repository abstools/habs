module ABS.Compiler.Utils 
    ( showQU
    , splitQU
    , showQA
    , splitQA
    , headToLower
    , errorPos, warnPos, showPos
    ) where

import qualified ABS.AST as ABS
import Data.List (intercalate)
import Data.Char (toLower)
import Debug.Trace (trace)

showQU :: ABS.QU -> String
showQU (ABS.U_ (ABS.U (_,ident))) = ident
showQU (ABS.QU (ABS.U (_,ident)) rest) = ident ++ "." ++ showQU rest

splitQU :: ABS.QU -> (String, String)
splitQU (ABS.U_ (ABS.U (_,ident))) = ("", ident)
splitQU (ABS.QU (ABS.U (_,qualIdent)) rest) = let (qualRest, ident) = splitQU rest
                                          in (qualIdent ++ "." ++ qualRest, ident)


showQA :: ABS.QA -> String
showQA (ABS.UA (ABS.U (_,ident))) = ident
showQA (ABS.LA (ABS.L (_,ident))) = ident
showQA (ABS.QA (ABS.U (_,ident)) rest) = ident ++ "." ++ showQA rest


splitQA :: ABS.QA -> (String, String)
splitQA (ABS.UA (ABS.U (_,ident))) = ("", ident)
splitQA (ABS.LA (ABS.L (_,ident))) = ("", ident)
splitQA (ABS.QA (ABS.U (_,qualIdent)) rest) = let (qualRest, ident) = splitQA rest
                                              in (qualIdent ++ "." ++ qualRest, ident)


-- | Used for turning an ABS type variable (e.g. A,B,DgFx) to HS type variable (a,b,dgFx)
headToLower :: String -> String
headToLower (x:xs) = toLower x : xs


-- | Querying a statement AST
--

errorPos :: (Int, Int) -> String -> a
errorPos pos msg = error ("[error #" ++ showPos pos ++ "]" ++  msg)

warnPos :: (Int,Int) -> String -> a -> a
warnPos  pos msg = trace ("[warning #" ++ showPos pos ++ "]" ++  msg)

showPos :: (Int, Int) -> String
showPos (row,col) = show row ++ ":" ++ show col
