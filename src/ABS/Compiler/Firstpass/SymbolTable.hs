{-# LANGUAGE LambdaCase #-}
module ABS.Compiler.Firstpass.SymbolTable 
    ( globalSTs
    ) where

import ABS.Compiler.Firstpass.Base
import ABS.AST
import ABS.Compiler.Utils

import qualified Data.Map as M
import Data.Maybe (fromMaybe)
import Data.List (find)

-- | Computes the symboltables of all the parsed modules
--
-- NB: Will loop on circular module dependencies.
globalSTs :: [Module] -> M.Map ModuleName SymbolTable
globalSTs ms = foldl (\ acc m@(Module qu es is ds _) -> 
                          M.insert (showQU qu) ( -- the symboltable indexed by the modulename
                                                     extends ds $ -- fetch the super interfaces only for the extended-interface symbols 
                                                     exports es $ -- adjust the exported flags of all the symbols
                                                     localST m `unionDup` imports is -- union the local and imported symbols
                                                    ) acc) 
               M.empty -- start with an empty globalSTs
               ms      -- traverse *all* the modules

    where
      -- builds a symboltable only from imports section.
      imports = foldl (\ acc i -> case i of
        AnyImport YesForeign qas -> foldl 
                                    (\ acc' qa -> let (prefix,iden) = splitQA qa
                                                  in M.insert (SN iden (Just (prefix, True))) (SV Foreign False) acc') 
                                    acc 
                                    qas
        AnyFromImport YesForeign qas from  -> foldl 
                                              (\ acc' qa -> M.insert (SN (showQA qa) (Just (showQU from, False))) (SV Foreign False) acc') 
                                              acc 
                                              qas
        StarFromImport YesForeign _ -> acc -- now ignore, todo: requires ghc-api
        StarFromImport NoForeign from -> let sTyp = showQU from
                                             exported = M.filter (\ (SV _ isExported) -> isExported) $ fromMaybe (error "no such module") $ M.lookup sTyp $ globalSTs ms
                                         in M.unionWith (error "duplicate symbol") acc (M.mapKeys (\ k -> case normalize k of
                                                                                            SN n Nothing -> SN n $ Just (sTyp, False)
                                                                                            n -> n)
                                                                                            exported)

        AnyImport NoForeign qas -> foldl (\ acc' qa -> let (prefix,iden) = splitQA qa
                                                       in singleImport True prefix iden acc') acc qas
        AnyFromImport NoForeign qas from -> foldl (\ acc' qa -> singleImport False (showQU from) (showQA qa)  acc') acc qas
                         ) M.empty
        where
          singleImport isQualified sTyp sIden  = let lookupRemote st' = (\ (SV v _) -> SV v False) $ -- don't inherit the exportness
                                                            snd $ M.elemAt 0 $ M.filterWithKey (\ (SN n' _) (SV _ isExported) -> isExported && sIden == n') st'
                                                 in M.insert (SN sIden $ Just (sTyp, isQualified))
                                                   (lookupRemote $ fromMaybe (error "no such module") $ M.lookup sTyp $ globalSTs ms)

      -- for each symbol in the symbol table, adjust its export flag, taking into account the exports section. 
      exports es st = foldl (\ acc e -> case e of
        AnyExport qas -> foldl (\ acc' qa -> let 
           (prefix,iden) = splitQA qa
           mk = find (\ (SN sname mImported) -> sname == iden && case mImported of
                                                                   Just (smodule,True) -> smodule == prefix   
                                                                   _ -> True) (M.keys acc') -- todo
                                             in maybe (error "symbol not in scope") (\ k -> M.adjust (\ (SV v _) -> SV v True) k acc') mk) acc qas
        AnyFromExport qas from -> foldl 
                                  (\ acc' qa -> M.insertWith (\ _ (SV v _) -> SV v True) 
                                  (SN (showQA qa) (Just (showQU from, False))) (error "symbol not declared") acc') 
                                  acc 
                                  qas
        StarFromExport qu -> M.mapWithKey (\ (SN _ from) (SV v exported) -> if from == Just (showQU qu, False)
                                                                              then SV v True
                                                                              else SV v exported) acc
        StarExport -> acc
                            ) st es

      -- for each symbol in the symbol table, if it is an ExtendedInterface, fetch its required Super Interfaces.
      extends ds st = foldl (\ acc (AnnDecl _ d) -> case d of
         DExtends (U (_, i)) xs _ ->  foldl (\ acc' qu ->
                                          let 
                                              (mqual,s) = splitQU qu
                                              Just mk = find (\ (SN sname mimported) -> sname == s && (null mqual ||
                                                                                                        mimported == Just (mqual, True))) 
                                                        (M.keys acc') -- todo
                                          in case M.lookup mk acc' of
                                               Just (SV (Interface farMs farSupers) _) -> 
                                                   M.adjust (\ (SV (Interface nearMs nearSupers) isExported) -> 
                                                                 SV (Interface nearMs (M.insert (normalize mk) farMs
                                                                                                  $ nearSupers `M.union` farSupers)) isExported)   (SN i Nothing) acc'
                                               _ -> error "cannot find parent interface to extend"                                             
                                     ) acc xs
         _ -> acc
                            ) st ds


      -- | Only checks the in-module decls and builds an "unfinished" global symbol table
      localST :: Module -> SymbolTable
      localST (Module _ es _ decls _) = foldl (\ acc (AnnDecl _ d) -> f d acc) 
                                 M.empty -- start with an empty symbol table
                                 decls   -- traverse all the local declarations
          where

            f (DType (U (_, s)) _) = insertDup (SN s Nothing) 
                                                       (SV Datatype sureExported)

            f (DData (U (_, s)) cs) = insertDup (SN s Nothing) 
                                                        (SV Datatype sureExported)
                                              . (\ st -> foldl (flip (f' s)) st cs) -- add also its constructors

            f (DFun _ (L (_, s)) _ _) = insertDup (SN s Nothing) 
                                                          (SV Function sureExported)

            f (DInterf (U (_, s)) ms') = insertDup (SN s Nothing) 
              (SV (Interface 
                (map (\ (MethSig as _ (L (_,s')) ps) -> (s', if any (\case 
                                                                  Ann (AnnNoType (ESinglConstr qu)) -> showQU qu == "HTTPCallable"
                                                                  _ -> False
                                                                ) as
                                                             then map (\ (FormalPar _ (L (_,str))) -> str) ps
                                                             else [])) ms') -- add also its direct methods
                                                                M.empty) -- no super interfaces
                                                            sureExported)

            f (DClass (U (_, s)) _ _ _) = insertDup (SN s Nothing) 
                                                            (SV Class sureExported)

            f (DException (SinglConstrIdent (U (_, s)))) = insertDup (SN s Nothing) 
                                                                    (SV Exception sureExported)

            -- synonyms
            f (DFunPoly _ i _ _ _) = f (DFun undefined i undefined undefined)
            f (DDataPoly i _ cs) = f (DData i cs)
            f (DTypePoly i _ _) = f (DType i undefined)
            f (DClassPar i _ _ _ _) = f (DClass i undefined undefined undefined)
            f (DClassImplements i _ _ _ _) = f (DClass i undefined undefined undefined)
            f (DClassParImplements i _ _ _ _ _) = f (DClass i undefined undefined undefined)
            f (DExtends i _ ms') = f (DInterf i ms') -- the super interfaces are filled later by the function extends
            f (DException (ParamConstrIdent i _)) = f (DException (SinglConstrIdent i))               

            -- data constructors
            f' dname (SinglConstrIdent (U (_, s))) acc = insertDup (SN s Nothing) 
                                                              (SV (Datacons dname) sureExported) acc
            f' dname (ParamConstrIdent i args) acc = 
              -- add also all the accessors as functions
              foldl (\ acc' arg -> case arg of
                                    RecordConstrType _ (L (_,s)) -> insertDup (SN s Nothing) (SV Function sureExported) acc'
                                    _ -> acc') (f' dname (SinglConstrIdent i) acc) args

            -- this is needed because, "export *;" will export *ONLY* the locally-defined symbols
            -- later, the "exports" Haskell function will check also for individual (non-star) exports
            sureExported = any (\case
                                StarExport -> True
                                _ -> False) es

      -- utils
      unionDup = M.unionWith (error "duplicate symbol")
      insertDup = M.insertWithKey (\ (SN s _) _ _ -> error ("already declared: " ++ s))
      normalize (SN i k) = SN i $ fmap (\ (n,_) -> (n, False)) k 
                                              
      
