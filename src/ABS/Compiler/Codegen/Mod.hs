{-# LANGUAGE ImplicitParams, QuasiQuotes, LambdaCase, PatternSynonyms #-}
module ABS.Compiler.Codegen.Mod 
    ( tModul
    ) where

import ABS.Compiler.Firstpass.Base
import ABS.Compiler.Utils
import ABS.Compiler.Codegen.Dec (tDataInterfDecl,tRestDecl)
import ABS.Compiler.Codegen.Stm (tMethod)
import ABS.Compiler.CmdOpt

import qualified ABS.AST as ABS
import qualified Language.Haskell.Exts.Simple.Syntax as HS
import Language.Haskell.Exts.QQ (hs, dec)

import qualified Data.Map as M (Map, lookup, keys, empty, foldlWithKey, member, toAscList)
import Data.List (find, partition)
import Data.Maybe (fromJust, fromMaybe, mapMaybe)
import Data.Char (isUpper)

tModul :: (?absFileName::String) 
       => ABS.Module 
       -> M.Map ModuleName SymbolTable 
       -> HS.Module
tModul (ABS.Module thisModuleQU exports imports decls maybeMain) allSymbolTables = HS.Module 
  (Just $ HS.ModuleHead 
    (HS.ModuleName thisModuleName)
    Nothing
    -- TRANSLATED EXPORTS OF THE ABS-PROGRAM
    (Just $ HS.ExportSpecList $ (case maybeMain of
                   ABS.JustBlock _ -> ((HS.EVar $ HS.UnQual $ HS.Ident "main") :) -- adds main to the export list
                   ABS.NoBlock -> id) $ concatMap tExport exports)
  )
  -- MODULE PRAGMAS
  [ HS.LanguagePragma [ HS.Ident "NoImplicitPrelude" -- for not importing haskell's prelude
                             , HS.Ident "ExistentialQuantification" -- for heterogeneous collections
                             , HS.Ident "MultiParamTypeClasses" -- for subtyping
                             , HS.Ident "ScopedTypeVariables" -- in ABS typevars are scoped(over the whole function),in Haskell not by default
                             , HS.Ident "FlexibleContexts" -- for some type inference of methods
                             , HS.Ident "PartialTypeSignatures" -- for inferring Eq,Ord contexts. Requires GHC>=7.10
                             , HS.Ident "NamedWildCards" -- needed for subtyping hints together with partialtypesignatures
                             , HS.Ident "LambdaCase" -- easier codegen for exceptions extension
                             , HS.Ident "OverloadedStrings" -- for Scotty REST API
                             , HS.Ident "TemplateHaskell" -- for generating subtyping fmaps through genifunctors
                             ]
    -- -fwarn-missing-methods:  for making error the missing ABS class methods
    -- -fno-ignore-asserts:  for not ignoring asserts (which is the default in Haskell)
    -- all other warnings are ignored
  , HS.OptionsPragma (Just HS.GHC) "-w -Werror -fforce-recomp -fwarn-missing-methods -fno-ignore-asserts"
  ]
  -- fixed IMPORTS HEADER
  ((if nostdlib cmdOpt
    then id
    else
      (HS.ImportDecl (HS.ModuleName "ABS.StdLib")
                     False
                     False
                     False
                     Nothing
                     Nothing
                     Nothing
                     :))
  ([ HS.ImportDecl (HS.ModuleName "ABS.Runtime")
                     False
                     False
                     False
                     Nothing
                     Nothing
                     Nothing
  , HS.ImportDecl (HS.ModuleName "Data.Function" )
                  False
                  False
                  False
                  Nothing
                  Nothing
                  (Just $ HS.ImportSpecList False [HS.IVar $ HS.Symbol "."])
  , HS.ImportDecl (HS.ModuleName "Control.Applicative")
                  False
                  False
                  False
                  Nothing
                  Nothing
                  (Just $ HS.ImportSpecList False [HS.IVar $ HS.Symbol "<*>", HS.IVar $ HS.Symbol "*>"])
  , HS.ImportDecl (HS.ModuleName "Control.Monad")
                  False
                  False
                  False
                  Nothing
                  Nothing
                  (Just $ HS.ImportSpecList False [HS.IVar $ HS.Symbol "=<<"])

  , HS.ImportDecl (HS.ModuleName "Control.Applicative")
                  True
                  False
                  False
                  Nothing
                  (Just $ HS.ModuleName "I'")
                  (Just $ HS.ImportSpecList False [HS.IVar $ HS.Ident "pure"])
  , HS.ImportDecl (HS.ModuleName "Data.IORef")
                  True
                  False
                  False
                  Nothing
                  (Just $ HS.ModuleName "I'")
                  (Just $ HS.ImportSpecList False [HS.IVar $ HS.Ident "newIORef", HS.IVar $ HS.Ident "readIORef", HS.IVar $ HS.Ident "writeIORef", HS.IVar $ HS.Ident "atomicModifyIORef'"])
  , HS.ImportDecl (HS.ModuleName "Control.Monad.Trans.Class")
                  True
                  False
                  False
                  Nothing
                  (Just $ HS.ModuleName "I'")
                  (Just $ HS.ImportSpecList False [HS.IVar $ HS.Ident "lift"])
  , HS.ImportDecl (HS.ModuleName "Control.Monad")
                  True
                  False
                  False
                  Nothing
                  (Just $ HS.ModuleName "I'")
                  (Just $ HS.ImportSpecList False [HS.IVar $ HS.Ident "Monad", HS.IVar $ HS.Ident "when", HS.IVar $ HS.Ident "sequence", HS.IVar $ HS.Ident "join"])
  , HS.ImportDecl (HS.ModuleName "Prelude")
                  True
                  False
                  False
                  Nothing
                  (Just $ HS.ModuleName "I'")
                  -- Ord and Show have to be IThingAll, so we can define custom instances
                  (Just $ HS.ImportSpecList False [HS.IVar $ HS.Ident "IO", HS.IVar $ HS.Ident "Eq", HS.IThingAll $ HS.Ident "Ord", HS.IThingAll $ HS.Ident "Show", HS.IVar $ HS.Ident "undefined", HS.IVar $ HS.Ident "error", HS.IVar $ HS.Ident "negate", HS.IVar $ HS.Ident "fromIntegral", HS.IVar $ HS.Ident "mapM_", HS.IVar $ HS.Ident "id"])
  , HS.ImportDecl (HS.ModuleName "Unsafe.Coerce")
                  True
                  False
                  False
                  Nothing
                  (Just $ HS.ModuleName "I'")
                  (Just $ HS.ImportSpecList False [HS.IVar $ HS.Ident "unsafeCoerce"])
  , HS.ImportDecl (HS.ModuleName "Control.Concurrent")
                  True
                  False
                  False
                  Nothing
                  (Just $ HS.ModuleName "I'")
                  (Just $ HS.ImportSpecList False [HS.IVar $ HS.Ident "ThreadId"])
  , HS.ImportDecl (HS.ModuleName "Control.Concurrent.MVar")
                  True
                  False
                  False
                  Nothing
                  (Just $ HS.ModuleName "I'")
                  (Just $ HS.ImportSpecList False [HS.IVar $ HS.Ident "isEmptyMVar", HS.IVar $ HS.Ident "readMVar"])
  , HS.ImportDecl (HS.ModuleName "Control.Exception")
                  False
                  False
                  False
                  Nothing
                  Nothing
                  (Just $ HS.ImportSpecList False [HS.IVar $ HS.Ident "assert"])
  , HS.ImportDecl (HS.ModuleName "Control.Exception")
                  True
                  False
                  False
                  Nothing
                  (Just $ HS.ModuleName "I'")
                  (Just $ HS.ImportSpecList False [HS.IThingAll $ HS.Ident "Exception", HS.IVar $ HS.Ident "SomeException", HS.IVar $ HS.Ident "throwTo", HS.IVar $ HS.Ident "throw"])
  , HS.ImportDecl (HS.ModuleName "Data.Dynamic")
                  True
                  False
                  False
                  Nothing
                  (Just $ HS.ModuleName "I'")
                  (Just $ HS.ImportSpecList False [HS.IVar $ HS.Ident "toDyn", HS.IVar $ HS.Ident "fromDynamic"])
  , HS.ImportDecl (HS.ModuleName "Data.Map.Lazy")
                  True
                  False
                  False
                  Nothing
                  (Just $ HS.ModuleName "I'")
                  (Just $ HS.ImportSpecList False [HS.IVar $ HS.Ident "lookup", HS.IVar $ HS.Ident "insert"])
  , HS.ImportDecl (HS.ModuleName "Web.Scotty")
                  True
                  False
                  False
                  Nothing
                  (Just $ HS.ModuleName "I'")
                  (Just $ HS.ImportSpecList False [HS.IVar $ HS.Ident "get", HS.IVar $ HS.Ident "param", HS.IVar $ HS.Ident "json", HS.IVar $ HS.Ident "raise"])
  , HS.ImportDecl (HS.ModuleName "Data.Generics.Genifunctors")
                  True
                  False
                  False
                  Nothing
                  (Just $ HS.ModuleName "I'")
                  (Just $ HS.ImportSpecList False [HS.IVar $ HS.Ident "genFmap"])
  ]
  -- TRANSLATED IMPORTS OF THE ABS-PROGRAM
  ++ concatMap tImport imports
  )) 

 -- TRANSLATED TOP-LEVEL DECLARATIONS
 (let ?st = st 
  in let (dataDecls, restDecls) = partition (\case 
                                            ABS.DData _ _ -> True
                                            ABS.DDataPoly _ _ _ -> True
                                            ABS.DInterf _ _ -> True
                                            ABS.DExtends _ _ _ -> True
                                            _ -> False) $ map (\ (ABS.AnnDecl _ d) -> d) decls
     in [dec|default (Int,Rat)|] -- better for type inference of numeric variables
        : concatMap tDataInterfDecl dataDecls
        ++ [HS.SpliceDecl [hs|return []|]]
        -- Generate a GeniFunctor if it is a polymorphic datatype
        ++ foldl (\ acc -> \case 
                              ABS.DDataPoly (ABS.U (_,tid)) _ _ -> HS.PatBind (HS.PVar $ HS.Ident $ "fmap'" ++ tid) (HS.UnGuardedRhs $ 
                                                                      HS.SpliceExp $ HS.ParenSplice $ [hs|I'.genFmap|] `HS.App` HS.TypQuote (HS.UnQual $ HS.Ident tid)) Nothing : acc
                              _ -> acc) [] dataDecls
        ++ concatMap tRestDecl restDecls 
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
             -- in HS, typeclass methods must be explicitly exported and existential wrapper constructor
             Interface _ _ -> [ EThingAll $ HS.UnQual $ HS.Ident $ showQA iden ++ "'"
                              , EThingAll $ HS.UnQual $ HS.Ident $ showQA iden]
             -- in ABS the dataconstructor can be exported without its datatype!
             -- this is wrong, then you cannot do anything with that data-value
             -- in HS we *must* export its datatype also
             Datacons dname _ _ _ -> [HS.EThingWith HS.NoWildcard (HS.UnQual $ HS.Ident dname)
                               [HS.ConName $ HS.Ident $ showQA iden]]
             Exception -> [EThingAll $ HS.UnQual $ HS.Ident $ showQA iden,
                          HS.EVar $ HS.UnQual $ HS.Ident $ headToLower $ showQA iden ++ "'" -- myException' smart constructor
                         ]
             Class _ _ -> [EThingAll $ HS.UnQual $ HS.Ident $ showQA iden
                      ,HS.EVar $ HS.UnQual $ HS.Ident $ "smart'" ++ showQA iden -- class smart constructor
                      ,HS.EVar $ HS.UnQual $ HS.Ident $ "init'" ++ showQA iden -- class init block 
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
             Interface _ _ -> [EThingAll $ maybeQual $ HS.Ident $ showQA iden]
             -- in ABS the dataconstructor can be exported without its datatype!
             -- this is wrong, then you cannot do anything with that data-value
             -- in HS we *must* export its datatype also
             Datacons dname _ _ _ -> [HS.EThingWith HS.NoWildcard (maybeQual $ HS.Ident dname)
                               [HS.ConName $ HS.Ident $ showQA iden]]
             Exception -> [EThingAll $ maybeQual $ HS.Ident $ showQA iden,
                          HS.EVar $ maybeQual $ HS.Ident $ headToLower $ showQA iden ++ "'" -- myException' smart constructor
                         ]
             Class _ _ -> [EThingAll $ maybeQual $ HS.Ident $ showQA iden,
                          HS.EVar $ maybeQual $ HS.Ident $ headToLower $ showQA iden ++ "'" -- class smart constructor
                         ]
             -- function, datatype, type synonym, foreign
             _ -> [HS.EVar $ maybeQual $ HS.Ident $ showQA iden]
                                                      ) es

    tImport :: (?absFileName::String) => ABS.Import -> [HS.ImportDecl]
    tImport (ABS.StarFromImport _ityp qu) = [HS.ImportDecl (HS.ModuleName $ showQU qu) 
                                                 False -- qualified?
                                                 False False Nothing Nothing -- irrelevant
                                                 (Just $ HS.ImportSpecList True [HS.IVar $ HS.Ident "main"])] -- hiding main

    tImport (ABS.AnyImport _ityp qas) = mapMaybe (\ qa ->
                                            let (prefix, iden) = splitQA qa
                                            in if prefix == "ABS.StdLib." && not (nostdlib cmdOpt)
                                               then Nothing
                                               else Just $ HS.ImportDecl (HS.ModuleName prefix)
                                                           True -- qualified?
                                                           False False Nothing Nothing -- irrelevant
                                                           (Just $ HS.ImportSpecList False $ tImport' True prefix iden) -- only import this 1 symbol (normally many,  but grammar limitation)
                                                    ) qas

        

    tImport (ABS.AnyFromImport _ityp qas qu) = if showQU qu == "ABS.StdLib" && not (nostdlib cmdOpt)
                                               then [] -- ignore if it is absstdlib
                                               else [HS.ImportDecl (HS.ModuleName $ showQU qu) 
                                                  False -- qualified?
                                                  False False Nothing Nothing -- irrelevant
                                                  (Just $ HS.ImportSpecList False $ concatMap (tImport' False (showQU qu) . showQA) qas)] -- only  import those symbols

    tImport' :: IsQualified -> String -> String -> [HS.ImportSpec]
    tImport' isQualified moduleName iden = 
          let 
              symbolName = SN iden $ Just (moduleName, isQualified)
              SV symbolValue _ = fromJust $ M.lookup symbolName st
          in case symbolValue of
               -- same applies as exportedxport rules
               Interface _ _ -> [HS.IThingAll $ HS.Ident iden]
               Datacons dname _ _ _ -> [HS.IThingWith (HS.Ident dname)
                                       [HS.ConName $ HS.Ident iden]]
               Exception -> [HS.IThingAll $ HS.Ident iden,
                              HS.IVar $ HS.Ident $ headToLower iden ++ "'" -- myException' smart constructor
                           ]
               Class _ _ -> [HS.IThingAll $ HS.Ident iden,
                          HS.IVar $ HS.Ident $ headToLower iden ++ "'" -- class smart constructor
                       ]
               Foreign -> [if isUpper $ head iden 
                           then HS.IThingAll $ HS.Ident iden
                           else HS.IVar $ HS.Ident iden]
               -- function, datatype, type synonym
               _ -> [HS.IVar $ HS.Ident iden]
                                                      
    tMain :: (?st::SymbolTable) => ABS.MaybeBlock -> [HS.Decl]
    tMain ABS.NoBlock = []
    tMain (ABS.JustBlock block) = 
      let callableMethods :: [(String,String,[String])] -- interface, method, formalparams
          callableMethods = M.foldlWithKey (\ acc k v -> case k of 
              SN iname Nothing -> case v of
                SV (Interface dmethods _imethods) _ -> foldl (\ acc' (mname, mfparams) -> 
                  case mfparams of
                   Nothing -> acc'
                   Just fparams -> (iname,mname,fparams):acc') [] dmethods ++ acc
                _ -> acc
              _ -> acc
            ) [] ?st
          makeCallable :: (String,String,[String]) -> HS.Stmt
          makeCallable (iname,mname,fparams) = HS.Qualifier
            [hs|I'.get $(HS.Lit $ HS.String $ "/call/:httpName'/" ++ mname) (do
                  objs' <- I'.lift (I'.readIORef apiStore')
                  httpName' <- I'.param "httpName'"
                  case I'.lookup httpName' objs' of
                    Just obj' -> I'.json =<< $casts
                    Nothing -> I'.raise "no such object name")
            |]
            where ipat = iname ++ " obj''"
                  mcalled = foldl (\ acc str -> [hs|$acc <*> I'.param $(HS.Lit $ HS.String str)|]) 
                                   [hs|I'.pure $(HS.Var $ HS.UnQual $ HS.Ident mname)|] fparams
                  subInterfaces = foldl (\ acc -> \case 
                                           (SN iname' _, SV (Interface _ extends) _) -> if SN iname Nothing `M.member` extends then iname':acc else acc  
                                           _ -> acc
                                        ) [] (M.toAscList ?st)  
                  makeSubCast acc iname' = [hs|case I'.fromDynamic obj' of
                      Just (__ipat'__) -> do
                        mapplied' <- $mcalled
                        I'.lift (get =<< obj'' <!> mapplied')
                      Nothing -> $acc|]
                      where ipat' = iname' ++ " obj''"
                  casts = foldl makeSubCast [hs|case I'.fromDynamic obj' of
                                                    Just (__ipat__) -> do
                                                      mapplied' <- $mcalled
                                                      I'.lift (get =<< obj'' <!> mapplied')
                                                    Nothing -> I'.raise "wrong interface"|] subInterfaces 
          scottyAction = if null callableMethods
                         then [hs|I'.pure ()|]
                         else HS.Do $ map makeCallable callableMethods
      in [[dec|main = main_is' (\ this -> $(tMethod block [] M.empty "" [] False ABS.TInfer)) ($scottyAction)|]] 
         -- no params, no fields, empty class-name, no alone-methods


pattern EThingAll x = HS.EThingWith (HS.EWildcard 1) x []