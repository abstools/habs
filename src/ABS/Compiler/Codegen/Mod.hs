{-# LANGUAGE ImplicitParams, QuasiQuotes #-}
module ABS.Compiler.Codegen.Mod 
    ( tModul
    ) where

import ABS.Compiler.Firstpass.Base
import ABS.Compiler.Utils
import ABS.Compiler.Codegen.Dec (tDecl)
import ABS.Compiler.Codegen.Stm (tMethod)


import qualified ABS.AST as ABS
import qualified Language.Haskell.Exts.Syntax as HS
import Language.Haskell.Exts.QQ (dec)
import Language.Haskell.Exts.SrcLoc (noLoc)

import qualified Data.Map as M (Map, lookup, keys, empty)
import Data.List (find)
import Data.Maybe (fromJust, fromMaybe)

tModul :: ABS.Module -> M.Map ModuleName SymbolTable -> HS.Module
tModul (ABS.Modul modulQTyp exports imports decls maybeMain) allSymbolTables = 
  HS.Module noLoc (HS.ModuleName mname)
       -- MODULE PRAGMAS
       [HS.LanguagePragma noLoc [ HS.Ident "NoImplicitPrelude" -- for not importing haskell's prelude
                                , HS.Ident "ExistentialQuantification" -- for heterogeneous collections
                                , HS.Ident "MultiParamTypeClasses" -- for subtyping
                                , HS.Ident "PatternSignatures" -- for inlining type annotations
                                , HS.Ident "FlexibleContexts" -- for some type inference of methods
                                , HS.Ident "DeriveDataTypeable" -- for defining ABS exceptions (exceptions are dynamically typed in haskell)
                                ]
       -- -fwarn-missing-methods:  for making error the missing ABS class methods
       -- -fno-ignore-asserts:  for not ignoring asserts (which is the default in Haskell)
       -- all other warnings are ignored
       , HS.OptionsPragma noLoc (Just HS.GHC) "-w -Werror -fforce-recomp -fwarn-missing-methods -fno-ignore-asserts"
       ]
       Nothing
       -- TRANSLATED EXPORTS OF THE ABS-PROGRAM
       (Just $ (case maybeMain of
                  ABS.JustBlock _ _ -> ((HS.EVar $ HS.UnQual $ HS.Ident "main") :) -- adds main to the export list
                  ABS.NoBlock -> id) $ concatMap tExport exports)

       -- fixed IMPORTS HEADER 
       ([ HS.ImportDecl { HS.importModule = HS.ModuleName "ABS.Runtime"
                        , HS.importQualified = False
                        , HS.importAs = Nothing
                        , HS.importLoc = noLoc, HS.importSrc = False, HS.importPkg = Nothing, HS.importSpecs = Nothing, HS.importSafe = False
                        }
        , HS.ImportDecl { HS.importModule = HS.ModuleName "ABS.StdLib"
                        , HS.importQualified = False
                        , HS.importAs = Nothing
                        , HS.importLoc = noLoc, HS.importSrc = False, HS.importPkg = Nothing, HS.importSpecs = Nothing, HS.importSafe = False
                        } 
        , HS.ImportDecl { HS.importModule = HS.ModuleName "Data.Function" 
                        , HS.importQualified = False
                        , HS.importAs = Nothing
                        , HS.importSpecs = Just (False,[HS.IVar (HS.Symbol ".")])
                        , HS.importLoc = noLoc, HS.importSrc = False, HS.importSafe = False, HS.importPkg = Nothing
                        }
        , HS.ImportDecl { HS.importModule = HS.ModuleName "Control.Applicative" 
                        , HS.importQualified = False
                        , HS.importAs = Nothing
                        , HS.importSpecs = Just (False,[HS.IVar (HS.Symbol "<$>"), HS.IVar (HS.Symbol "<*>")])
                        , HS.importLoc = noLoc, HS.importSrc = False, HS.importSafe = False, HS.importPkg = Nothing
                        }
        , HS.ImportDecl { HS.importModule = HS.ModuleName "Control.Applicative" 
                        , HS.importQualified = True
                        , HS.importAs = Just (HS.ModuleName "I'")
                        , HS.importSpecs = Just (False,[HS.IVar (HS.Ident "pure")])
                        , HS.importLoc = noLoc, HS.importSrc = False, HS.importSafe = False, HS.importPkg = Nothing
                        }
        , HS.ImportDecl { HS.importModule = HS.ModuleName "Data.IORef" 
                        , HS.importQualified = True
                        , HS.importAs = Just (HS.ModuleName "I'")
                        , HS.importSpecs = Just (False,[HS.IVar (HS.Ident "newIORef"), HS.IVar (HS.Ident "readIORef"), HS.IVar (HS.Ident "writeIORef")])
                        , HS.importLoc = noLoc, HS.importSrc = False, HS.importSafe = False, HS.importPkg = Nothing
                        }
        , HS.ImportDecl { HS.importModule = HS.ModuleName "Control.Monad.IO.Class" 
                        , HS.importQualified = True
                        , HS.importAs = Just (HS.ModuleName "I'")
                        , HS.importSpecs = Just (False,[HS.IVar (HS.Ident "liftIO")])
                        , HS.importLoc = noLoc, HS.importSrc = False, HS.importSafe = False, HS.importPkg = Nothing
                        }
        , HS.ImportDecl { HS.importModule = HS.ModuleName "Prelude" 
                        , HS.importQualified = True
                        , HS.importAs = Just (HS.ModuleName "I'")
                        , HS.importSpecs = Just (False,[HS.IVar $ HS.Ident "Eq", HS.IThingAll $ HS.Ident "Ord", HS.IThingAll $ HS.Ident "Show", HS.IVar $ HS.Ident "putStrLn"])
                        , HS.importLoc = noLoc, HS.importSrc = False, HS.importSafe = False, HS.importPkg = Nothing
                        }
        , HS.ImportDecl { HS.importModule = HS.ModuleName "Unsafe.Coerce" 
                        , HS.importQualified = True
                        , HS.importAs = Just (HS.ModuleName "I'")
                        , HS.importSpecs = Just (False,[HS.IVar (HS.Ident "unsafeCoerce")])
                        , HS.importLoc = noLoc, HS.importSrc = False, HS.importSafe = False, HS.importPkg = Nothing
                        }
        ]
       -- TRANSLATED IMPORTS OF THE ABS-PROGRAM
       ++ map tImport imports
       ) 

       -- TRANSLATED TOP-LEVEL DECLARATIONS
       (let ?st = st 
        in concatMap (\ (ABS.AnnDec _ d) -> tDecl d) decls
           ++ tMain maybeMain)

    where
      mname = showQType modulQTyp
      st = fromJust $ M.lookup mname allSymbolTables 

      tExport :: ABS.Export -> [HS.ExportSpec]
      tExport ABS.StarExport = [HS.EModuleContents $ HS.ModuleName mname]
      tExport (ABS.StarFromExport qtyp) = [HS.EModuleContents $ HS.ModuleName $ showQType qtyp]
      tExport (ABS.AnyExport es) = concatMap (\ iden -> 
        let symbolName = fromMaybe (error "symbol not in scope") $ find (\ (SN sname mimported) -> sname == showAnyIdent iden && case mimported of
                                                                                                                       Nothing -> True
                                                                                                                       Just (_, False) -> True
                                                                                                                       _ -> False) (M.keys st)
            SV symbolValue _ = fromJust $ M.lookup symbolName st
        in case symbolValue of
             -- in ABS the interface methods are implicitly exported, 
             -- in HS, typeclass methods must be explicitly exported
             Interface _ _ -> [HS.EThingAll $ HS.UnQual $ HS.Ident $ showAnyIdent iden]
             -- in ABS the dataconstructor can be exported without its datatype!
             -- this is wrong, then you cannot do anything with that data-value
             -- in HS we *must* export its datatype also
             Datacons dname -> [HS.EThingWith (HS.UnQual $ HS.Ident dname)
                               [HS.ConName $ HS.Ident $ showAnyIdent iden]]
             Exception -> [HS.EThingAll $ HS.UnQual $ HS.Ident $ showAnyIdent iden,
                          HS.EVar $ HS.UnQual $ HS.Ident $ headToLower $ showAnyIdent iden ++ "'" -- myException' smart constructor
                         ]
             Class -> [HS.EThingAll $ HS.UnQual $ HS.Ident $ showAnyIdent iden,
                          HS.EVar $ HS.UnQual $ HS.Ident $ headToLower $ showAnyIdent iden ++ "'" -- class smart constructor
                         ]
             -- function, datatype, type synonym, foreign
             _ -> [HS.EVar $ HS.UnQual $ HS.Ident $ showAnyIdent iden] ) es

      tExport (ABS.AnyFromExport es qtyp) = concatMap (\ iden -> 
        let symbolName@(SN _ (Just (mname',isQualified'))) = fromMaybe (error "symbol not in scope") $ 
                                                             find (\ (SN sname mimported) -> sname == showAnyIdent iden && case mimported of
                                                                                                                 Just (mname'',_) -> mname'' == showQType qtyp
                                                                                                                 _ -> False) (M.keys st)
            SV symbolValue _ = fromJust $ M.lookup symbolName st
            maybeQual = if isQualified'
                        then HS.Qual (HS.ModuleName mname')
                        else HS.UnQual
        in case symbolValue of
             -- in ABS the interface methods are implicitly exported, 
             -- in HS, typeclass methods must be explicitly exported
             Interface _ _ -> [HS.EThingAll $ maybeQual $ HS.Ident $ showAnyIdent iden]
             -- in ABS the dataconstructor can be exported without its datatype!
             -- this is wrong, then you cannot do anything with that data-value
             -- in HS we *must* export its datatype also
             Datacons dname -> [HS.EThingWith (maybeQual $ HS.Ident dname)
                               [HS.ConName $ HS.Ident $ showAnyIdent iden]]
             Exception -> [HS.EThingAll $ maybeQual $ HS.Ident $ showAnyIdent iden,
                          HS.EVar $ maybeQual $ HS.Ident $ headToLower $ showAnyIdent iden ++ "'" -- myException' smart constructor
                         ]
             Class -> [HS.EThingAll $ maybeQual $ HS.Ident $ showAnyIdent iden,
                          HS.EVar $ maybeQual $ HS.Ident $ headToLower $ showAnyIdent iden ++ "'" -- class smart constructor
                         ]
             -- function, datatype, type synonym, foreign
             _ -> [HS.EVar $ maybeQual $ HS.Ident $ showAnyIdent iden]
                                                      ) es

      tImport :: ABS.Import -> HS.ImportDecl
      tImport (ABS.StarFromImport _ityp qtyp) = HS.ImportDecl noLoc (HS.ModuleName $ showQType qtyp) 
                                                False -- qualified?
                                                False False Nothing Nothing -- irrelevant
                                                (Just (True, [HS.IVar $ HS.Ident "main"])) -- hiding main

      tImport (ABS.AnyImport _ityp ttyp aid) = HS.ImportDecl noLoc (HS.ModuleName $ showTType ttyp)
                                               True -- qualified?
                                               False False Nothing Nothing -- irrelevant
                                               (Just (False, tImport' (showTType ttyp, False) aid)) -- only import this 1 symbol (normally many,  but grammar limitation)

      tImport (ABS.AnyFromImport _ityp aids qtyp) = HS.ImportDecl noLoc (HS.ModuleName (showQType qtyp)) 
                                                    False -- qualified?
                                                    False False Nothing Nothing -- irrelevant
                                                    (Just (False, concatMap (tImport' (showQType qtyp, True)) aids)) -- only  import those symbols

      tImport' :: (ModuleName,IsQualified) -> ABS.AnyIdent -> [HS.ImportSpec]
      tImport' k iden = 
          let symbolName = SN (showAnyIdent iden) $ Just k
              SV symbolValue _ = fromJust $ M.lookup symbolName st
          in case symbolValue of
               -- same applies as export rules
               Interface _ _ -> [HS.IThingAll $ HS.Ident $ showAnyIdent iden]
               Datacons dname -> [HS.IThingWith (HS.Ident dname)
                                       [HS.ConName $ HS.Ident $ showAnyIdent iden]]
               Exception -> [HS.IThingAll $ HS.Ident $ showAnyIdent iden,
                              HS.IVar $ HS.Ident $ headToLower $ showAnyIdent iden ++ "'" -- myException' smart constructor
                           ]
               Class -> [HS.IThingAll $ HS.Ident $ showAnyIdent iden,
                          HS.IVar $ HS.Ident $ headToLower $ showAnyIdent iden ++ "'" -- class smart constructor
                       ]
               -- function, datatype, type synonym, foreign
               _ -> [HS.IVar $ HS.Ident $ showAnyIdent iden]
                                                      
      tMain :: (?st::SymbolTable) => ABS.MaybeBlock -> [HS.Decl]
      tMain ABS.NoBlock = []
      tMain (ABS.JustBlock _ block) = [[dec| main = main_is' (\ this -> $(tMethod block [] M.empty "")) |]]-- no params, no fields, empty class-name


