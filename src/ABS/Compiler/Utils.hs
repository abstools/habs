module ABS.Compiler.Utils 
    ( showQType
    , showTType
    , splitQType
    , showAnyIdent
    , tTypeToQType
    , headToLower
    , errorPos, warnPos, showPos
    ) where

import qualified ABS.AST as ABS
import Data.List (intercalate)
import Data.Char (toLower)
import Debug.Trace (trace)

showQType :: ABS.QType -> String
showQType (ABS.QTyp qsegs) = intercalate "." $ 
                             map (\ (ABS.QTypeSegmen (ABS.UIdent (_,s))) -> s) qsegs

splitQType :: ABS.QType -> (String, String)
splitQType (ABS.QTyp qsegs) = let ABS.QTypeSegmen (ABS.UIdent (_, ident)) = last qsegs
                                  qualPrefix = init qsegs
                              in (showQType $ ABS.QTyp qualPrefix, ident)

showTType :: ABS.TType -> String
showTType = showQType . tTypeToQType

tTypeToQType :: ABS.TType -> ABS.QType
tTypeToQType (ABS.TTyp tsegs) = ABS.QTyp $ map (\ (ABS.TTypeSegmen iden) -> ABS.QTypeSegmen iden) tsegs

showAnyIdent :: ABS.AnyIdent -> String
showAnyIdent (ABS.AnyIden (ABS.LIdent (_, s))) = s
showAnyIdent (ABS.AnyTyIden (ABS.UIdent (_, s))) = s

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
