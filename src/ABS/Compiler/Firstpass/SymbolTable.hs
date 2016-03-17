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
globalSTs ms = foldl (\ acc m@(Modul qtyp es is ds _) -> 
                          M.insert (showQType qtyp) ( -- the symboltable indexed by the modulename
                                                     extends ds $ -- fetch the super interfaces only for the extended-interface symbols 
                                                     exports es $ -- adjust the exported flags of all the symbols
                                                     localST m `unionDup` imports is -- union the local and imported symbols
                                                    ) acc) 
               M.empty -- start with an empty globalSTs
               ms      -- traverse *all* the modules

    where
      -- builds a symboltable only from imports section.
      imports is = foldl (\ acc i -> case i of
        AnyImport ForeignImport ttyp iden -> M.insert (SN (showAnyIdent iden) (Just $ (showTType ttyp, True))) (SV Foreign False) acc
        AnyFromImport ForeignImport idents from  -> foldl (\ acc' iden -> M.insert (SN (showAnyIdent iden) (Just (showQType from, False))) (SV Foreign False) acc') acc idents
        StarFromImport ForeignImport _ -> acc -- todo, requires ghc-api
        AnyImport NormalImport ttyp iden -> singleImport (tTypeToQType ttyp) iden True acc
        AnyFromImport NormalImport idents qtyp -> foldl (\ acc' iden -> singleImport qtyp iden False acc') acc idents
        StarFromImport NormalImport qtyp -> starImport qtyp acc
                         ) M.empty is
        where
          singleImport qtyp iden isQualified = let sIden = showAnyIdent iden
                                                   sTyp = showQType qtyp
                                                   lookupRemote st' = (\ (SV v _) -> SV v False) $ -- don't inherit the exportness
                                                            snd $ M.elemAt 0 $ M.filterWithKey (\ (SN n' _) (SV _ isExported) -> isExported && sIden == n') st'
                                               in M.insert (SN sIden $ Just (sTyp, isQualified))
                                                  (lookupRemote $ fromMaybe (error "no such module") $ M.lookup sTyp $ globalSTs ms)

          starImport qtyp st = let sTyp = showQType qtyp
                                   exported = M.filter (\ (SV _ isExported) -> isExported) $ fromMaybe (error "no such module") $ M.lookup sTyp $ globalSTs ms
                               in M.unionWith (error "duplicate symbol") st (M.mapKeys (\ k -> case normalize k of
                                                                                            SN n Nothing -> SN n $ Just (sTyp, False)
                                                                                            n -> n)
                                                                                            exported)


      -- for each symbol in the symbol table, adjust its export flag, taking into account the exports section. 
      exports es st = foldl (\ acc e -> case e of
        AnyExport idents -> foldl (\ acc' iden -> let mk = find (\ (SN sname mimported) -> sname == (showAnyIdent iden) && case mimported of
                                                                                                                       Nothing -> True
                                                                                                                       Just (_, False) -> True
                                                                                                                       _ -> False) (M.keys acc') -- todo
                                                in maybe (error "symbol not in scope") (\ k -> M.adjust (\ (SV v _) -> SV v True) k acc') mk) acc idents
        AnyFromExport idents qtyp -> foldl (\ acc' iden -> M.insertWith (\ _ (SV v _) -> SV v True) 
                                          (SN (showAnyIdent iden) (Just (showQType qtyp, False))) (error "symbol not declared") acc') acc idents
        StarFromExport qtyp -> M.mapWithKey (\ (SN _ from) (SV v exported) -> if from == Just (showQType qtyp, False)
                                                                            then SV v True
                                                                            else SV v exported) acc
        StarExport -> acc
                            ) st es

      -- for each symbol in the symbol table, if it is an ExtendedInterface, fetch its required Super Interfaces.
      extends ds st = foldl (\ acc (AnnDec _ d) -> case d of
         ExtendsDecl (UIdent (_, i)) xs _ ->  foldl (\ acc' (QTyp qsegs) ->
                                          let 
                                              mqual = init qsegs
                                              QTypeSegmen (UIdent (_, s)) = last qsegs
                                              Just mk = find (\ (SN sname mimported) -> sname == s && if null mqual
                                                                                                   then True
                                                                                                   else mimported == Just (showQType (QTyp mqual), True)) (M.keys acc') -- todo
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
      localST (Modul _ es _ decls _) = foldl (\ acc (AnnDec _ d) -> f d acc) 
                                 M.empty -- start with an empty symbol table
                                 decls   -- traverse all the local declarations
          where

            f (TypeDecl (UIdent (_, s)) _) = insertDup (SN s Nothing) 
                                                       (SV Datatype sureExported)

            f (DataDecl (UIdent (_, s)) cs) = insertDup (SN s Nothing) 
                                                        (SV Datatype sureExported)
                                              . (\ st -> foldl (flip (f' s)) st cs) -- add also its constructors

            f (FunDecl _ (LIdent (_, s)) _ _) = insertDup (SN s Nothing) 
                                                          (SV Function sureExported)

            f (InterfDecl (UIdent (_, s)) ms') = insertDup (SN s Nothing) 
                                                           (SV (Interface 
                                                                (map (\ (AnnMethSig _ (MethSig _ (LIdent (_,s')) _)) -> s') ms') -- add also its direct methods
                                                                M.empty) -- no super interfaces
                                                            sureExported)

            f (ClassDecl (UIdent (_, s)) _ _ _) = insertDup (SN s Nothing) 
                                                            (SV Class sureExported)

            f (ExceptionDecl (SinglConstrIdent (UIdent (_, s)))) = insertDup (SN s Nothing) 
                                                                    (SV Exception sureExported)

            -- synonyms
            f (FunParDecl _ i _ _ _) = f (FunDecl undefined i undefined undefined)
            f (DataParDecl i _ cs) = f (DataDecl i cs)
            f (TypeParDecl i _ _) = f (TypeDecl i undefined)
            f (ClassParamDecl i _ _ _ _) = f (ClassDecl i undefined undefined undefined)
            f (ClassImplements i _ _ _ _) = f (ClassDecl i undefined undefined undefined)
            f (ClassParamImplements i _ _ _ _ _) = f (ClassDecl i undefined undefined undefined)
            f (ExtendsDecl i _ ms') = f (InterfDecl i ms') -- the super interfaces are filled later by the function extends
            f (ExceptionDecl (ParamConstrIdent i _)) = f (ExceptionDecl (SinglConstrIdent i))               

            -- data constructors
            f' dname (SinglConstrIdent (UIdent (_, s))) = insertDup (SN s Nothing) 
                                                              (SV (Datacons dname) sureExported)
            f' dname (ParamConstrIdent i _) = f' dname (SinglConstrIdent i)

            -- this is needed because, "export *;" will export *ONLY* the locally-defined symbols
            -- later, the "exports" Haskell function will check also for individual (non-star) exports
            sureExported = any (\case
                                StarExport -> True
                                _ -> False) es

      -- utils
      unionDup = M.unionWith (error "duplicate symbol")
      insertDup = M.insertWithKey (\ (SN s _) _ _ -> error ("already declared: " ++ s))
      normalize (SN i k) = SN i $ fmap (\ (n,_) -> (n, False)) k 
                                              
      
