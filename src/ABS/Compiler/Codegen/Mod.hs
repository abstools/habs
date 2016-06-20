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

import qualified Data.Map as M (Map, lookup, keys, empty)
import Data.List (find)
import Data.Maybe (fromJust, fromMaybe)
import Data.Char (isUpper)

tModul :: (?absFileName::String) 
       => ABS.Module 
       -> M.Map ModuleName SymbolTable 
       -> HS.Module
tModul (ABS.Module thisModuleQU exports imports decls maybeMain) allSymbolTables = HS.Module
  (mkLocFromQU thisModuleQU) -- adds {-# LINE #-} pragma 
  (HS.ModuleName thisModuleName)
  -- MODULE PRAGMAS
  [ HS.LanguagePragma noLoc' [ HS.Ident "NoImplicitPrelude" -- for not importing haskell's prelude
                             , HS.Ident "ExistentialQuantification" -- for heterogeneous collections
                             , HS.Ident "MultiParamTypeClasses" -- for subtyping
                             , HS.Ident "ScopedTypeVariables" -- in ABS typevars are scoped(over the whole function),in Haskell not by default
                             , HS.Ident "FlexibleContexts" -- for some type inference of methods
                             , HS.Ident "PartialTypeSignatures" -- for inferring Eq,Ord contexts. Requires GHC>=7.10
                             , HS.Ident "LambdaCase" -- easier codegen for exceptions extension
                             ]
    -- -fwarn-missing-methods:  for making error the missing ABS class methods
    -- -fno-ignore-asserts:  for not ignoring asserts (which is the default in Haskell)
    -- all other warnings are ignored
  , HS.OptionsPragma noLoc' (Just HS.GHC) "-w -Werror -fforce-recomp -fwarn-missing-methods -fno-ignore-asserts"
  ] Nothing
  -- TRANSLATED EXPORTS OF THE ABS-PROGRAM
  (Just $ (case maybeMain of
                  ABS.JustBlock _ -> ((HS.EVar $ HS.UnQual $ HS.Ident "main") :) -- adds main to the export list
                  ABS.NoBlock -> id) $ concatMap tExport exports)

  -- fixed IMPORTS HEADER 
  ([ HS.ImportDecl { HS.importModule = HS.ModuleName "ABS.Runtime"
                   , HS.importQualified = False
                   , HS.importAs = Nothing
                   , HS.importLoc = noLoc', HS.importSrc = False, HS.importPkg = Nothing, HS.importSpecs = Nothing, HS.importSafe = False
                   }
   , HS.ImportDecl { HS.importModule = HS.ModuleName "ABS.StdLib"
                   , HS.importQualified = False
                   , HS.importAs = Nothing
                   , HS.importLoc = noLoc', HS.importSrc = False, HS.importPkg = Nothing, HS.importSpecs = Nothing, HS.importSafe = False
                   } 
  , HS.ImportDecl { HS.importModule = HS.ModuleName "Data.Function" 
                  , HS.importQualified = False
                  , HS.importAs = Nothing
                  , HS.importSpecs = Just (False,[HS.IVar $ HS.Symbol "."])
                  , HS.importLoc = noLoc', HS.importSrc = False, HS.importSafe = False, HS.importPkg = Nothing
                  }
  , HS.ImportDecl { HS.importModule = HS.ModuleName "Control.Applicative" 
                  , HS.importQualified = False
                  , HS.importAs = Nothing
                  , HS.importSpecs = Just (False,[HS.IVar $ HS.Symbol "<*>", HS.IVar $ HS.Symbol "*>"])
                  , HS.importLoc = noLoc', HS.importSrc = False, HS.importSafe = False, HS.importPkg = Nothing
                  }
  , HS.ImportDecl { HS.importModule = HS.ModuleName "Control.Monad" 
                  , HS.importQualified = False
                  , HS.importAs = Nothing
                  , HS.importSpecs = Just (False,[HS.IVar $ HS.Symbol "=<<"])
                  , HS.importLoc = noLoc', HS.importSrc = False, HS.importSafe = False, HS.importPkg = Nothing
                  }
  , HS.ImportDecl { HS.importModule = HS.ModuleName "Control.Applicative" 
                  , HS.importQualified = True
                  , HS.importAs = Just (HS.ModuleName "I'")
                  , HS.importSpecs = Just (False,[HS.IVar $ HS.Ident "pure"])
                  , HS.importLoc = noLoc', HS.importSrc = False, HS.importSafe = False, HS.importPkg = Nothing
                  }
  , HS.ImportDecl { HS.importModule = HS.ModuleName "Data.IORef" 
                  , HS.importQualified = True
                  , HS.importAs = Just (HS.ModuleName "I'")
                  , HS.importSpecs = Just (False,[HS.IVar $ HS.Ident "newIORef", HS.IVar $ HS.Ident "readIORef", HS.IVar $ HS.Ident "writeIORef"])
                  , HS.importLoc = noLoc', HS.importSrc = False, HS.importSafe = False, HS.importPkg = Nothing
                  }
  , HS.ImportDecl { HS.importModule = HS.ModuleName "Control.Monad.Trans.Class" 
                  , HS.importQualified = True
                  , HS.importAs = Just (HS.ModuleName "I'")
                  , HS.importSpecs = Just (False,[HS.IVar $ HS.Ident "lift"])
                  , HS.importLoc = noLoc', HS.importSrc = False, HS.importSafe = False, HS.importPkg = Nothing
                  }
  , HS.ImportDecl { HS.importModule = HS.ModuleName "Control.Monad" 
                  , HS.importQualified = True
                  , HS.importAs = Just (HS.ModuleName "I'")
                  , HS.importSpecs = Just (False,[HS.IVar $ HS.Ident "when", HS.IVar $ HS.Ident "sequence", HS.IVar $ HS.Ident "join"])
                  , HS.importLoc = noLoc', HS.importSrc = False, HS.importSafe = False, HS.importPkg = Nothing
                  }
  , HS.ImportDecl { HS.importModule = HS.ModuleName "Prelude" 
                  , HS.importQualified = True
                  , HS.importAs = Just (HS.ModuleName "I'")
                  -- Ord and Show have to be IThingAll, so we can define custom instances
                  , HS.importSpecs = Just (False,[HS.IVar $ HS.Ident "IO", HS.IVar $ HS.Ident "Eq", HS.IThingAll $ HS.Ident "Ord", HS.IThingAll $ HS.Ident "Show", HS.IVar $ HS.Ident "undefined", HS.IVar $ HS.Ident "error", HS.IVar $ HS.Ident "negate", HS.IVar $ HS.Ident "fromIntegral", HS.IVar $ HS.Ident "mapM_"])
                  , HS.importLoc = noLoc', HS.importSrc = False, HS.importSafe = False, HS.importPkg = Nothing
                  }
  , HS.ImportDecl { HS.importModule = HS.ModuleName "Unsafe.Coerce" 
                  , HS.importQualified = True
                  , HS.importAs = Just (HS.ModuleName "I'")
                  , HS.importSpecs = Just (False,[HS.IVar $ HS.Ident "unsafeCoerce"])
                  , HS.importLoc = noLoc', HS.importSrc = False, HS.importSafe = False, HS.importPkg = Nothing
                  }
   , HS.ImportDecl { HS.importModule = HS.ModuleName "Control.Concurrent" 
                  , HS.importQualified = True
                  , HS.importAs = Just (HS.ModuleName "I'")
                  , HS.importSpecs = Just (False,[HS.IVar $ HS.Ident "ThreadId"])
                  , HS.importLoc = noLoc', HS.importSrc = False, HS.importSafe = False, HS.importPkg = Nothing
                  }
  , HS.ImportDecl { HS.importModule = HS.ModuleName "Control.Concurrent.MVar" 
                  , HS.importQualified = True
                  , HS.importAs = Just (HS.ModuleName "I'")
                  , HS.importSpecs = Just (False,[HS.IVar $ HS.Ident "isEmptyMVar", HS.IVar $ HS.Ident "readMVar"])
                  , HS.importLoc = noLoc', HS.importSrc = False, HS.importSafe = False, HS.importPkg = Nothing
                  }
  , HS.ImportDecl { HS.importModule = HS.ModuleName "Control.Exception" 
                  , HS.importQualified = False
                  , HS.importAs = Nothing
                  , HS.importSpecs = Just (False,[HS.IVar $ HS.Ident "assert"])
                  , HS.importLoc = noLoc', HS.importSrc = False, HS.importSafe = False, HS.importPkg = Nothing
                  }
  , HS.ImportDecl { HS.importModule = HS.ModuleName "Control.Exception" 
                  , HS.importQualified = True
                  , HS.importAs = Just (HS.ModuleName "I'")
                  , HS.importSpecs = Just (False,[HS.IThingAll $ HS.Ident "SomeException", HS.IVar $ HS.Ident "throwTo"])
                  , HS.importLoc = noLoc', HS.importSrc = False, HS.importSafe = False, HS.importPkg = Nothing
                  }
  ]
  -- TRANSLATED IMPORTS OF THE ABS-PROGRAM
  ++ concatMap tImport imports
  ) 

 -- TRANSLATED TOP-LEVEL DECLARATIONS
 (let ?st = st 
  in [dec|default (Int,Rat)|] -- better for type inference of numeric variables
     : concatMap (\ (ABS.AnnDecl _ d) -> tDecl d) decls
     ++ tMain maybeMain)

  where
    thisModuleName = showQU thisModuleQU
    st = fromJust $ M.lookup thisModuleName allSymbolTables 

    tExport :: ABS.Export -> [HS.ExportSpec]
    tExport ABS.StarExport = [HS.EModuleContents $ HS.ModuleName thisModuleName]
    tExport (ABS.StarFromExport qtyp) = [HS.EModuleContents $ HS.ModuleName $ showQU qtyp]
    tExport (ABS.AnyExport es) = concatMap (\ iden -> 
        let symbolName = fromMaybe (error "symbol not in scope") $ find (\ (SN sname mimported) -> sname == showQA iden && case mimported of
                                                                                                                       Nothing -> True
                                                                                                                       Just (_, False) -> True
                                                                                                                       _ -> False) (M.keys st)
            SV symbolValue _ = fromJust $ M.lookup symbolName st
        in case symbolValue of
             -- in ABS the interface methods are implicitly exported, 
             -- in HS, typeclass methods must be explicitly exported
             Interface _ _ -> [HS.EThingAll $ HS.UnQual $ HS.Ident $ showQA iden]
             -- in ABS the dataconstructor can be exported without its datatype!
             -- this is wrong, then you cannot do anything with that data-value
             -- in HS we *must* export its datatype also
             Datacons dname -> [HS.EThingWith (HS.UnQual $ HS.Ident dname)
                               [HS.ConName $ HS.Ident $ showQA iden]]
             Exception -> [HS.EThingAll $ HS.UnQual $ HS.Ident $ showQA iden,
                          HS.EVar $ HS.UnQual $ HS.Ident $ headToLower $ showQA iden ++ "'" -- myException' smart constructor
                         ]
             Class -> [HS.EThingAll $ HS.UnQual $ HS.Ident $ showQA iden,
                          HS.EVar $ HS.UnQual $ HS.Ident $ headToLower $ showQA iden ++ "'" -- class smart constructor
                         ]
             -- function, datatype, type synonym, foreign
             _ -> [HS.EVar $ HS.UnQual $ HS.Ident $ showQA iden] ) es

    tExport (ABS.AnyFromExport es qtyp) = concatMap (\ iden -> 
        let symbolName@(SN _ (Just (mname',isQualified'))) = fromMaybe (error "symbol not in scope") $ 
                                                             find (\ (SN sname mimported) -> sname == showQA iden && case mimported of
                                                                                                                 Just (mname'',_) -> mname'' == showQU qtyp
                                                                                                                 _ -> False) (M.keys st)
            SV symbolValue _ = fromJust $ M.lookup symbolName st
            maybeQual = if isQualified'
                        then HS.Qual (HS.ModuleName mname')
                        else HS.UnQual
        in case symbolValue of
             -- in ABS the interface methods are implicitly exported, 
             -- in HS, typeclass methods must be explicitly exported
             Interface _ _ -> [HS.EThingAll $ maybeQual $ HS.Ident $ showQA iden]
             -- in ABS the dataconstructor can be exported without its datatype!
             -- this is wrong, then you cannot do anything with that data-value
             -- in HS we *must* export its datatype also
             Datacons dname -> [HS.EThingWith (maybeQual $ HS.Ident dname)
                               [HS.ConName $ HS.Ident $ showQA iden]]
             Exception -> [HS.EThingAll $ maybeQual $ HS.Ident $ showQA iden,
                          HS.EVar $ maybeQual $ HS.Ident $ headToLower $ showQA iden ++ "'" -- myException' smart constructor
                         ]
             Class -> [HS.EThingAll $ maybeQual $ HS.Ident $ showQA iden,
                          HS.EVar $ maybeQual $ HS.Ident $ headToLower $ showQA iden ++ "'" -- class smart constructor
                         ]
             -- function, datatype, type synonym, foreign
             _ -> [HS.EVar $ maybeQual $ HS.Ident $ showQA iden]
                                                      ) es

    tImport :: (?absFileName::String) => ABS.Import -> [HS.ImportDecl]
    tImport (ABS.StarFromImport _ityp qu) = [HS.ImportDecl (mkLocFromQU qu) (HS.ModuleName $ showQU qu) 
                                                 False -- qualified?
                                                 False False Nothing Nothing -- irrelevant
                                                 (Just (True, [HS.IVar $ HS.Ident "main"]))] -- hiding main

    tImport (ABS.AnyImport _ityp qas) = map (\ qa ->
                                            let (prefix, iden) = splitQA qa
                                            in HS.ImportDecl (mkLocFromQA qa) (HS.ModuleName prefix)
                                               True -- qualified?
                                               False False Nothing Nothing -- irrelevant
                                               (Just (False, tImport' True prefix iden)) -- only import this 1 symbol (normally many,  but grammar limitation)
                                                    ) qas

        

    tImport (ABS.AnyFromImport _ityp qas qu) = [HS.ImportDecl (mkLocFromQU qu) (HS.ModuleName $ showQU qu) 
                                                  False -- qualified?
                                                  False False Nothing Nothing -- irrelevant
                                                  (Just (False, concatMap (tImport' False (showQU qu) . showQA) qas))] -- only  import those symbols

    tImport' :: IsQualified -> String -> String -> [HS.ImportSpec]
    tImport' isQualified moduleName iden = 
          let 
              symbolName = SN iden $ Just (moduleName, isQualified)
              SV symbolValue _ = fromJust $ M.lookup symbolName st
          in case symbolValue of
               -- same applies as exportedxport rules
               Interface _ _ -> [HS.IThingAll $ HS.Ident iden]
               Datacons dname -> [HS.IThingWith (HS.Ident dname)
                                       [HS.ConName $ HS.Ident iden]]
               Exception -> [HS.IThingAll $ HS.Ident iden,
                              HS.IVar $ HS.Ident $ headToLower iden ++ "'" -- myException' smart constructor
                           ]
               Class -> [HS.IThingAll $ HS.Ident iden,
                          HS.IVar $ HS.Ident $ headToLower iden ++ "'" -- class smart constructor
                       ]
               Foreign -> [if isUpper $ head iden 
                           then HS.IThingAll $ HS.Ident iden
                           else HS.IVar $ HS.Ident iden]
               -- function, datatype, type synonym
               _ -> [HS.IVar $ HS.Ident iden]
                                                      
    tMain :: (?st::SymbolTable) => ABS.MaybeBlock -> [HS.Decl]
    tMain ABS.NoBlock = []
    tMain (ABS.JustBlock block) = [[dec|main = main_is' (\ this -> $(tMethod block [] M.empty "" [] False))|]] -- no params, no fields, empty class-name, no alone-methods


