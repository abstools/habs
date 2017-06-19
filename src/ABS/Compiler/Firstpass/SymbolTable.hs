{-# LANGUAGE LambdaCase #-}
module ABS.Compiler.Firstpass.SymbolTable 
    ( globalSTs
    ) where

import ABS.Compiler.Firstpass.Base
import ABS.AST
import ABS.Compiler.Utils
import ABS.Compiler.CmdOpt

import qualified Data.Map as M
import Data.Maybe (fromMaybe, mapMaybe)
import Data.List (find)

-- | Computes the symboltables of all the parsed modules
--
-- NB: Will loop on circular module dependencies.
globalSTs :: [Module] -> M.Map ModuleName SymbolTable
globalSTs ms = foldl (\ acc m@(Module qu es is ds _) -> 
                          M.insert (showQU qu) ( -- the symboltable indexed by the modulename
                                                     extends ds $ -- fetch the super interfaces only for the extended-interface symbols 
                                                     exports es $ -- adjust the exported flags of all the symbols
                                                     localST m `unionDup` imports is `unionDup` stdlibST -- union the local and imported symbols
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
        StarFromImport NoForeign from | showQU from == "ABS.StdLib" && not (nostdlib cmdOpt) -> acc -- ignore if it is absstdlib
        StarFromImport NoForeign from -> let sTyp = showQU from
                                             exported = M.filter (\ (SV _ isExported) -> isExported) $ fromMaybe (error "no such module") $ M.lookup sTyp $ globalSTs ms
                                         in M.union acc $ M.map (\ (SV v _) -> SV v False) 
                                                           $ M.mapKeys (\ k -> case normalize k of
                                                                                 SN n Nothing -> SN n $ Just (sTyp, False)
                                                                                 n -> n) exported

        AnyImport NoForeign qas -> foldl (\ acc' qa -> let (prefix,iden) = splitQA qa
                                                       in if prefix == "ABS.StdLib." && not (nostdlib cmdOpt)
                                                          then acc' -- ignore if it is absstdlib
                                                          else singleImport True prefix iden acc') acc qas
        AnyFromImport NoForeign qas from -> foldl (\ acc' qa -> if showQU from == "ABS.StdLib" && not (nostdlib cmdOpt)
                                                                then acc' -- ignore if it is absstdlib
                                                                else singleImport False (showQU from) (showQA qa)  acc') acc qas
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
                                                                   Just (smodule,_) -> smodule == prefix   
                                                                   Nothing -> True -- todo: or false?
                                                                   ) (M.keys acc') 
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

            f (DDataPoly i@(U (_, s)) tyvars cs) = insertDup (SN s Nothing) 
                                                        (SV Datatype sureExported)
                                              . (\ st -> foldl (flip (f' i tyvars)) st cs) -- add also its constructors

            f (DFunPoly ot (L (_, s)) tyvars params _) = insertDup (SN s Nothing) 
                                                          (SV (Function tyvars (map (\ (FormalPar t _) -> t) params) ot) sureExported)

            f (DInterf (U (_, s)) ms') = unionDup (insertDup (SN s Nothing) 
                (SV (Interface 
                  (map (\ (MethSig as _ (L (_,s')) ps) -> (s', if any (\case 
                                                                  Ann (AnnNoType (ESinglConstr qu)) -> showQU qu == "HTTPCallable"
                                                                  _ -> False
                                                                ) as
                                                             then Just $ map (\ (FormalPar _ (L (_,str))) -> str) ps
                                                             else Nothing)) ms') -- add also its direct methods
                                                                M.empty) -- no super interfaces
                                                            sureExported)
                  (M.fromList (map (\ (MethSig _ ot (L (_,s')) params) -> -- TODO: makes method to name-clash with functions
                                  (SN s' Nothing, SV (Function [] (map (\ (FormalPar t _) -> t) params) ot) False)
                              ) ms')))

            f (DClassParImplements (U (_, s)) formalPars interfs cb1 _ cb2) = unionDup 
              (insertDup (SN s Nothing) 
                         (SV (Class (map TSimple interfs) (map (\ (FormalPar t _) -> t) formalPars)) sureExported)
                         (M.fromList $ mapMaybe (\case 
                                          MethClassBody ot (L (_,s')) params _ -> Just (SN s' Nothing, SV (Function [] (map (\ (FormalPar t _) -> t) params) ot) False)
                                          _ -> Nothing
                                       ) (cb1++cb2)))

            f (DException (SinglConstrIdent (U (_, s)))) = insertDup (SN s Nothing) 
                                                                    (SV Exception sureExported)

            -- synonyms
            f (DFun t l params _) = f (DFunPoly t l [] params undefined)
            f (DData i cs) = f (DDataPoly i [] cs)
            f (DTypePoly i _ _) = f (DType i undefined)
            f (DClass i cb1 _ cb2) = f (DClassParImplements i [] [] cb1 undefined cb2)
            f (DClassPar i ps cb1 _ cb2) = f (DClassParImplements i ps [] cb1 undefined cb2)
            f (DClassImplements i interfs cb1 _ cb2) = f (DClassParImplements i [] interfs cb1 undefined cb2)
            f (DExtends i _ ms') = f (DInterf i ms') -- the super interfaces are filled later by the function extends
            f (DException (ParamConstrIdent i _)) = f (DException (SinglConstrIdent i))               
            f' d tyvars (SinglConstrIdent u) = f' d tyvars (ParamConstrIdent u [])

            -- data constructors
            f' d@(U (_,dname)) tyvars (ParamConstrIdent (U (_,cname)) args) = \ acc -> 
              -- this fold is for maybe adding any record field as a function
              foldr (\case
                        RecordConstrType t (L (_,s)) -> 
                              insertDup (SN s Nothing) (SV (Function tyvars [if null tyvars then TSimple (U_ d) else TPoly (U_ d) (map (TSimple . U_) tyvars)] t) sureExported)
                        _ -> id
                    )
                    -- this actually adds the constructor to the symboltable
                    (insertDup (SN cname Nothing) (SV (Datacons dname tyvars 
                        (map (\case RecordConstrType t _ -> t
                                    EmptyConstrType t -> t)  args) 
                        (if null tyvars then TSimple (U_ d) else TPoly (U_ d) (map (TSimple . U_) tyvars))) sureExported) acc)
                    args

            -- this is needed because, "export *;" will export *ONLY* the locally-defined symbols
            -- later, the "exports" Haskell function will check also for individual (non-star) exports
            sureExported = any (\case
                                StarExport -> True
                                _ -> False) es

      -- utils
      unionDup = M.union -- M.unionWith (\ x y -> error $ "duplicate symbol" ++ show x ++ show y)
      insertDup = M.insert -- M.insertWithKey (\ (SN s _) _ _ -> error ("already declared: " ++ s))
      normalize (SN i k) = SN i $ fmap (\ (n,_) -> (n, False)) k 
                                              
      
stdlibST :: SymbolTable
stdlibST = M.fromList $ map (\ (k,v) -> (SN k Nothing, SV v True))
  [ ("True", Datacons "Bool" [] [] $ TSimple $ U_ $ U ((0,0),"Bool"))
  , ("False", Datacons "Bool" [] [] $ TSimple $ U_ $ U ((0,0),"Bool"))
  , ("Nothing", Datacons "Maybe" [U ((0,0),"A")] [] $ TPoly (U_ $ U ((0,0),"Maybe")) [TSimple $ U_ $ U ((0,0),"A")])
  , ("Just", Datacons "Maybe" [U ((0,0),"A")] [TSimple $ U_ $ U ((0,0),"A")] $ TPoly (U_ $ U ((0,0),"Maybe")) [TSimple $ U_ $ U ((0,0),"A")])
  , ("Pair", Datacons "Pair" [U ((0,0),"A"),U ((0,0),"B")] [TSimple $ U_ $ U ((0,0),"A"),TSimple $ U_ $ U ((0,0),"B")] $ TPoly (U_ $ U ((0,0),"Pair")) [TSimple $ U_  $ U ((0,0),"A"),TSimple $ U_ $ U ((0,0),"B")])
  , ("fromJust", Function [U ((0,0),"A")] [TPoly (U_ $ U ((0,0),"Maybe")) [TSimple $ U_ $ U ((0,0),"A")]] (TSimple $ U_ $ U ((0,0),"A")))
  , ("truncate", Function [] [TSimple $ U_ $ U ((0,0),"Rat")] (TSimple $ U_ $ U ((0,0),"Int")))
  , ("Speed", Datacons "Resourcetype" [] [] $ TSimple $ U_ $ U ((0,0), "Resourcetype"))
  , ("Cores", Datacons "Resourcetype" [] [] $ TSimple $ U_ $ U ((0,0), "Resourcetype"))
  , ("Bandwidth", Datacons "Resourcetype" [] [] $ TSimple $ U_ $ U ((0,0), "Resourcetype"))
  , ("Memory", Datacons "Resourcetype" [] [] $ TSimple $ U_ $ U ((0,0), "Resourcetype"))
  , ("CostPerInterval", Datacons "Resourcetype" [] [] $ TSimple $ U_ $ U ((0,0), "Resourcetype"))
  , ("InfRat", Datacons "InfRat" [] [] $ TSimple $ U_ $ U ((0,0),"InfRat"))
  , ("Fin", Datacons "InfRat" [] [TSimple $ U_ $ U ((0,0),"Rat")] $ TSimple $ U_ $ U ((0,0),"InfRat"))
  , ("list", Function [U ((0,0),"A")] [TPoly (U_ $ U ((0,0),"List")) [TSimple $ U_ $ U ((0,0),"A")]] (TPoly (U_ $ U ((0,0),"List")) [TSimple $ U_ $ U ((0,0),"A")]) )
  , ("minimum", Function [U ((0,0),"A")] [TPoly (U_ $ U ((0,0),"List")) [TSimple $ U_ $ U ((0,0),"A")]] (TSimple $ U_ $ U ((0,0),"A")))
  , ("maximum", Function [U ((0,0),"A")] [TPoly (U_ $ U ((0,0),"List")) [TSimple $ U_ $ U ((0,0),"A")]] (TSimple $ U_ $ U ((0,0),"A")))
  , ("isJust", Function [U ((0,0),"A")] [TPoly (U_ $ U ((0,0),"Maybe")) [TSimple $ U_ $ U ((0,0),"A")]] (TSimple $ U_ $ U ((0,0),"Bool")))
  , ("toString", Function [U ((0,0),"A")] [TSimple $ U_ $ U ((0,0),"A")] (TSimple $ U_ $ U ((0,0),"String")))
  , ("substr", Function [] [TSimple $ U_ $ U ((0,0),"String"), TSimple $ U_ $ U ((0,0),"Int"), TSimple $ U_ $ U ((0,0),"Int")] (TSimple $ U_ $ U ((0,0),"String")))
  , ("strlen", Function [] [TSimple $ U_ $ U ((0,0),"String")] (TSimple $ U_ $ U ((0,0),"Int")))
  , ("length", Function [U ((0,0),"A")] [TPoly (U_ $ U ((0,0),"List")) [TSimple $ U_ $ U ((0,0),"A")]] (TSimple $ U_ $ U ((0,0),"Int")))
  , ("nth", Function [U ((0,0),"A")] [TPoly (U_ $ U ((0,0),"List")) [TSimple $ U_ $ U ((0,0),"A")], (TSimple $ U_ $ U ((0,0),"Int"))] (TSimple $ U_ $ U ((0,0),"A")))
  , ("head", Function [U ((0,0),"A")] [TPoly (U_ $ U ((0,0),"List")) [TSimple $ U_ $ U ((0,0),"A")]] (TSimple $ U_ $ U ((0,0),"A")))
  , ("tail", Function [U ((0,0),"A")] [TPoly (U_ $ U ((0,0),"List")) [TSimple $ U_ $ U ((0,0),"A")]] (TPoly (U_ $ U ((0,0),"List")) [TSimple $ U_ $ U ((0,0),"A")]))
  , ("isEmpty", Function [U ((0,0),"A")] [TPoly (U_ $ U ((0,0),"List")) [TSimple $ U_ $ U ((0,0),"A")]] (TSimple $ U_ $ U ((0,0),"Bool")))
  , ("concatenate", Function [U ((0,0),"A")] [TPoly (U_ $ U ((0,0),"List")) [TSimple $ U_ $ U ((0,0),"A")], TPoly (U_ $ U ((0,0),"List")) [TSimple $ U_ $ U ((0,0),"A")]] (TPoly (U_ $ U ((0,0),"List")) [TSimple $ U_ $ U ((0,0),"A")]))
  , ("without", Function [U ((0,0),"A")] [TPoly (U_ $ U ((0,0),"List")) [TSimple $ U_ $ U ((0,0),"A")], TSimple $ U_ $ U ((0,0),"A")] (TPoly (U_ $ U ((0,0),"List")) [TSimple $ U_ $ U ((0,0),"A")]))
  , ("fst", Function [U ((0,0),"A"),U ((0,0),"B")] [TPoly (U_ $ U ((0,0),"Pair")) [TSimple $ U_ $ U ((0,0),"A"), TSimple $ U_ $ U ((0,0),"B")]] (TSimple $ U_ $ U ((0,0),"A")))
  , ("snd", Function [U ((0,0),"A"),U ((0,0),"B")] [TPoly (U_ $ U ((0,0),"Pair")) [TSimple $ U_ $ U ((0,0),"A"), TSimple $ U_ $ U ((0,0),"B")]] (TSimple $ U_ $ U ((0,0),"B")))
  , ("max", Function [U ((0,0),"A")] [TSimple $ U_ $ U ((0,0),"A"), TSimple $ U_ $ U ((0,0),"A")] (TSimple $ U_ $ U ((0,0),"A")))
  , ("fstT", Function [U ((0,0),"A"),U ((0,0),"B"),U ((0,0),"C")] [TPoly (U_ $ U ((0,0),"Triple")) [TSimple $ U_ $ U ((0,0),"A"), TSimple $ U_ $ U ((0,0),"B"),  TSimple $ U_ $ U ((0,0),"C")]] (TSimple $ U_ $ U ((0,0),"A")))
  , ("sndT", Function [U ((0,0),"A"),U ((0,0),"B"),U ((0,0),"C")] [TPoly (U_ $ U ((0,0),"Triple")) [TSimple $ U_ $ U ((0,0),"A"), TSimple $ U_ $ U ((0,0),"B"),  TSimple $ U_ $ U ((0,0),"C")]] (TSimple $ U_ $ U ((0,0),"B")))
  , ("trd", Function [U ((0,0),"A"),U ((0,0),"B"),U ((0,0),"C")] [TPoly (U_ $ U ((0,0),"Triple")) [TSimple $ U_ $ U ((0,0),"A"), TSimple $ U_ $ U ((0,0),"B"),  TSimple $ U_ $ U ((0,0),"C")]] (TSimple $ U_ $ U ((0,0),"C")))
  , ("timeValue", Function [] [TSimple $ U_ $ U ((0,0),"Time")] $ TSimple $ U_ $ U ((0,0),"Rat"))
  , ("reverse", Function [U ((0,0),"A")] [TPoly (U_ $ U ((0,0),"List")) [TSimple $ U_ $ U ((0,0),"A")]] (TPoly (U_ $ U ((0,0),"List")) [TSimple $ U_ $ U ((0,0),"A")]))
  , ("appendright", Function [U ((0,0),"A")] [TPoly (U_ $ U ((0,0),"List")) [TSimple $ U_ $ U ((0,0),"A")], TSimple $ U_ $ U ((0,0),"A")] (TPoly (U_ $ U ((0,0),"List")) [TSimple $ U_ $ U ((0,0),"A")]))
  , ("finvalue", Function [] [TSimple $ U_ $ U ((0,0),"InfRat")] $ TSimple $ U_ $ U ((0,0),"Rat"))
  , ("set", Function [U ((0,0),"A")] [TPoly (U_ $ U ((0,0),"List")) [TSimple $ U_ $ U ((0,0),"A")]] (TPoly (U_ $ U ((0,0),"Set")) [TSimple $ U_ $ U ((0,0),"A")]) )
  , ("map", Function [U ((0,0),"A"),U ((0,0),"B")] [TPoly (U_ $ U ((0,0),"List")) [TPoly (U_ $ U ((0,0),"Pair")) [TSimple $ U_ $ U ((0,0),"A"), TSimple $ U_ $ U ((0,0),"B")]]] (TPoly (U_ $ U ((0,0),"Map")) [TSimple $ U_ $ U ((0,0),"A"), TSimple $ U_ $ U ((0,0),"B")]) )
  , ("lookupDefault", Function [U ((0,0),"A"),U ((0,0),"B")] [TPoly (U_ $ U ((0,0),"Map")) [TSimple $ U_ $ U ((0,0),"A"), TSimple $ U_ $ U ((0,0),"B")],TSimple $ U_ $ U ((0,0),"A"), TSimple $ U_ $ U ((0,0),"B")] (TSimple $ U_ $ U ((0,0),"B")) )
  , ("lookupUnsafe", Function [U ((0,0),"A"),U ((0,0),"B")] [TPoly (U_ $ U ((0,0),"Map")) [TSimple $ U_ $ U ((0,0),"A"), TSimple $ U_ $ U ((0,0),"B")],TSimple $ U_ $ U ((0,0),"A")] (TSimple $ U_ $ U ((0,0),"B")) )
  , ("lookup", Function [U ((0,0),"A"),U ((0,0),"B")] [TPoly (U_ $ U ((0,0),"Map")) [TSimple $ U_ $ U ((0,0),"A")],TSimple $ U_ $ U ((0,0),"A"), TSimple $ U_ $ U ((0,0),"B")] (TPoly (U_ $ U ((0,0),"Maybe")) [TSimple $ U_ $ U ((0,0),"B")]) )
  , ("put", Function [U ((0,0),"A"),U ((0,0),"B")] [TPoly (U_ $ U ((0,0),"Map")) [TSimple $ U_ $ U ((0,0),"A"), TSimple $ U_ $ U ((0,0),"B")],TSimple $ U_ $ U ((0,0),"A"), TSimple $ U_ $ U ((0,0),"B")] (TPoly (U_ $ U ((0,0),"Map")) [TSimple $ U_ $ U ((0,0),"A"), TSimple $ U_ $ U ((0,0),"B")] ))
  , ("removeKey", Function [U ((0,0),"A"),U ((0,0),"B")] [TPoly (U_ $ U ((0,0),"Map")) [TSimple $ U_ $ U ((0,0),"A"), TSimple $ U_ $ U ((0,0),"B")],TSimple $ U_ $ U ((0,0),"A")] (TPoly (U_ $ U ((0,0),"Map")) [TSimple $ U_ $ U ((0,0),"A"), TSimple $ U_ $ U ((0,0),"B")] ))
  , ("values", Function [U ((0,0),"A"),U ((0,0),"B")] [TPoly (U_ $ U ((0,0),"Map")) [TSimple $ U_ $ U ((0,0),"A"), TSimple $ U_ $ U ((0,0),"B")]] (TPoly (U_ $ U ((0,0),"List")) [TSimple $ U_ $ U ((0,0),"B")] ))
  , ("keys", Function [U ((0,0),"A"),U ((0,0),"B")] [TPoly (U_ $ U ((0,0),"Map")) [TSimple $ U_ $ U ((0,0),"A"), TSimple $ U_ $ U ((0,0),"B")]] (TPoly (U_ $ U ((0,0),"Set")) [TSimple $ U_ $ U ((0,0),"A")] ))
  , ("emptySet", Function [U ((0,0),"A")] [TPoly (U_ $ U ((0,0),"Set")) [TSimple $ U_ $ U ((0,0),"A")]] (TSimple $ U_ $ U ((0,0),"Bool") ))
  , ("EmptySet", Datacons "Set" [U ((0,0),"A")] [] $ TPoly (U_ $ U ((0,0),"Set")) [TSimple $ U_ $ U ((0,0),"A")])
  , ("remove", Function [U ((0,0),"A")] [TPoly (U_ $ U ((0,0),"Set")) [TSimple $ U_ $ U ((0,0),"A")],TSimple $ U_ $ U ((0,0),"A")] (TPoly (U_ $ U ((0,0),"Set")) [TSimple $ U_ $ U ((0,0),"A")] ))
  , ("size", Function [U ((0,0),"A")] [TPoly (U_ $ U ((0,0),"Set")) [TSimple $ U_ $ U ((0,0),"A")]] (TSimple $ U_ $ U ((0,0),"Int")))
  , ("take", Function [U ((0,0),"A")] [TPoly (U_ $ U ((0,0),"Set")) [TSimple $ U_ $ U ((0,0),"A")]] (TSimple $ U_ $ U ((0,0),"A")))
  , ("next", Function [U ((0,0),"A")] [TPoly (U_ $ U ((0,0),"Set")) [TSimple $ U_ $ U ((0,0),"A")]] (TPoly (U_ $ U ((0,0),"Pair")) [TPoly (U_ $ U ((0,0),"Set")) [TSimple $ U_ $ U ((0,0),"A")], TSimple $ U_ $ U ((0,0),"A")]))
  , ("hasNext", Function [U ((0,0),"A")] [TPoly (U_ $ U ((0,0),"Set")) [TSimple $ U_ $ U ((0,0),"A")]] (TSimple $ U_ $ U ((0,0),"Bool")))
  , ("insertElement", Function [U ((0,0),"A")] [TPoly (U_ $ U ((0,0),"Set")) [TSimple $ U_ $ U ((0,0),"A")],TSimple $ U_ $ U ((0,0),"A")] (TPoly (U_ $ U ((0,0),"Set")) [TSimple $ U_ $ U ((0,0),"A")] ))
  , ("EmptyMap", Datacons "Map" [U ((0,0),"A"), U ((0,0),"B")] [] $ TPoly (U_ $ U ((0,0),"Map")) [TSimple $ U_ $ U ((0,0),"A"), TSimple $ U_ $ U ((0,0),"B")])
  , ("insert", Function [U ((0,0),"A"), U ((0,0),"B")] [TPoly (U_ $ U ((0,0),"Pair")) [TSimple $ U_  $ U ((0,0),"A"),TSimple $ U_ $ U ((0,0),"B")], TPoly (U_ $ U ((0,0),"Map")) [TSimple $ U_ $ U ((0,0),"A"), TSimple $ U_ $ U ((0,0),"B")]] $ TPoly (U_ $ U ((0,0),"Map")) [TSimple $ U_ $ U ((0,0),"A"), TSimple $ U_ $ U ((0,0),"B")])
  , ("InsertAssoc", Datacons "Map" [U ((0,0),"A"), U ((0,0),"B")] [TPoly (U_ $ U ((0,0),"Pair")) [TSimple $ U_  $ U ((0,0),"A"),TSimple $ U_ $ U ((0,0),"B")], TPoly (U_ $ U ((0,0),"Map")) [TSimple $ U_ $ U ((0,0),"A"), TSimple $ U_ $ U ((0,0),"B")]] $ TPoly (U_ $ U ((0,0),"Map")) [TSimple $ U_ $ U ((0,0),"A"), TSimple $ U_ $ U ((0,0),"B")])  
  , ("DeploymentComponent", Interface (map (\x -> (x,Nothing)) ["load","total", "transfer","decrementResources", "incrementResources", "getName", "getCreationTime", "getStartupDuration", "getShutdownDuration", "getPaymentInterval", "getCostPerInterval", "getNumberOfCores", "acquire", "release", "shutdown_"]) M.empty)
  , ("CloudProvider", Interface (map (\x -> (x,Nothing)) ["prelaunchInstance","launchInstance","acquireInstance","releaseInstance", "shutdownInstance", "getAccumulatedCost", "shutdown", "setInstanceDescriptions", "addInstanceDescription", "removeInstanceDescription", "getInstanceDescriptions", "prelaunchInstanceNamed", "launchInstanceNamed"]) M.empty)
  , ("SimCloudProvider", Class [TSimple $ U_ $ U ((0,0), "CloudProvider")] [TSimple $ U_ $ U ((0,0),"String")])
  , ("addInstanceDescription", Function [] [TPoly (U_ $ U ((0,0),"Pair")) [TSimple $ U_  $ U ((0,0),"String"),TPoly (U_ $ U ((0,0),"Map")) [TSimple $ U_ $ U ((0,0),"Resourcetype"), TSimple $ U_ $ U ((0,0),"Rat")]]] (TSimple $ U_ $ U ((0,0),"Unit")))
  , ("prelaunchInstance", Function [] [TPoly (U_ $ U ((0,0),"Map")) [TSimple $ U_ $ U ((0,0),"Resourcetype"), TSimple $ U_ $ U ((0,0),"Rat")]] (TSimple $ U_ $ U ((0,0),"DeploymentComponent")))
  , ("prelaunchInstanceNamed", Function [] [TSimple $ U_ $ U ((0,0),"String")] (TSimple $ U_ $ U ((0,0),"DeploymentComponent")))
  , ("launchInstance", Function [] [TPoly (U_ $ U ((0,0),"Map")) [TSimple $ U_ $ U ((0,0),"Resourcetype"), TSimple $ U_ $ U ((0,0),"Rat")]] (TSimple $ U_ $ U ((0,0),"DeploymentComponent")))
  , ("launchInstanceNamed", Function [] [TSimple $ U_ $ U ((0,0),"String")] (TSimple $ U_ $ U ((0,0),"DeploymentComponent")))
  , ("acquireInstance", Function [] [TSimple $ U_ $ U ((0,0),"DeploymentComponent")] (TSimple $ U_ $ U ((0,0),"Bool")))
  , ("releaseInstance", Function [] [TSimple $ U_ $ U ((0,0),"DeploymentComponent")] (TSimple $ U_ $ U ((0,0),"Bool")))
  , ("shutdownInstance", Function [] [TSimple $ U_ $ U ((0,0),"DeploymentComponent")] (TSimple $ U_ $ U ((0,0),"Bool")))
  , ("getAccumulatedCost", Function [] [] (TSimple $ U_ $ U ((0,0),"Rat")))
  , ("setInstanceDescriptions", Function [] [TPoly (U_ $ U ((0,0),"Map")) [TSimple $ U_ $ U ((0,0),"String"), TPoly (U_ $ U ((0,0),"Map")) [TSimple $ U_ $ U ((0,0),"Resourcetype"), TSimple $ U_ $ U ((0,0),"Rat")]]] (TSimple $ U_ $ U ((0,0),"Unit")))
  , ("addInstanceDescription", Function [] [TPoly (U_ $ U ((0,0),"Pair")) [TSimple $ U_ $ U ((0,0),"String"), TPoly (U_ $ U ((0,0),"Map")) [TSimple $ U_ $ U ((0,0),"Resourcetype"), TSimple $ U_ $ U ((0,0),"Rat")]]] (TSimple $ U_ $ U ((0,0),"Unit")))
  , ("removeInstanceDescription", Function [] [TSimple $ U_ $ U ((0,0),"String")] (TSimple $ U_ $ U ((0,0),"Unit")))
  , ("getInstanceDescriptions", Function [] [] (TPoly (U_ $ U ((0,0),"Map")) [TSimple $ U_ $ U ((0,0),"Resourcetype"), TSimple $ U_ $ U ((0,0),"Rat")]))
  , ("shutdown", Function [] [] (TSimple $ U_ $ U ((0,0),"Unit")))
  , ("total", Function [] [TSimple $ U_ $ U ((0,0),"Resourcetype")] (TSimple $ U_ $ U ((0,0),"InfRat")))
  , ("getName", Function [] [] (TSimple $ U_ $ U ((0,0),"String")))
  ]