{-# LANGUAGE CPP, ImplicitParams, QuasiQuotes, LambdaCase #-}
module ABS.Compiler.Codegen.Dec where

import ABS.Compiler.Utils
import ABS.Compiler.Codegen.Base
import ABS.Compiler.Firstpass.Base
import ABS.Compiler.Codegen.Typ
import ABS.Compiler.Codegen.Exp
import ABS.Compiler.Codegen.Stm (tMethod)
import Language.Haskell.Exts.QQ (hs, dec, pat, ty)

import Control.Applicative ((<|>))
import Control.Monad.Trans.Reader (runReader)
import Data.Maybe (mapMaybe, isJust)
import qualified Data.Map as M
import qualified ABS.AST as ABS
import qualified Language.Haskell.Exts.Syntax as HS
import Data.List (find)

tDecl :: (?absFileName::String, ?st::SymbolTable) => ABS.Decl -> [HS.Decl]

-- Normalizations
tDecl (ABS.DFun fReturnTyp fid params body) = tDecl (ABS.DFunPoly fReturnTyp fid [] params body) -- normalize to no type variables
tDecl (ABS.DType tid typ) = tDecl (ABS.DTypePoly tid [] typ) -- type synonym with no type variables
tDecl (ABS.DData tid constrs) =  tDecl (ABS.DDataPoly tid [] constrs) -- just parametric datatype with empty list of type variables
tDecl (ABS.DInterf tid ms) = tDecl (ABS.DExtends tid [] ms) 
tDecl (ABS.DClass tident fdecls maybeBlock mdecls) = tDecl (ABS.DClassParImplements tident [] [] fdecls maybeBlock mdecls)
tDecl (ABS.DClassPar tident params fdecls maybeBlock mdecls) = tDecl (ABS.DClassParImplements tident params [] fdecls maybeBlock mdecls)
tDecl (ABS.DClassImplements tident imps fdecls maybeBlock mdecls) = tDecl (ABS.DClassParImplements tident [] imps fdecls maybeBlock mdecls)


-- Functions
tDecl (ABS.DFunPoly fReturnTyp (ABS.L (fpos,fid)) tyvars params body) = [
        -- note: trick because of bug in ghc-7.10 https://ghc.haskell.org/trac/ghc/ticket/10519
        -- in ghc>=8 the typeclass wildcard should be the context after forall typevars.
        -- NB: we assume here that the habs transcompiler is compiled with the same GHC compiler as the ABS executable itself
#if MIN_VERSION_GLASGOW_HASKELL(8,0,1,0)
        HS.TypeSig noLoc' [HS.Ident fid] (HS.TyForall (Just $ map (\(ABS.U (_, tident)) -> HS.UnkindedVar $ HS.Ident $ headToLower tident) tyvars) [HS.WildCardA Nothing] $
#else
        HS.TypeSig noLoc' [HS.Ident fid] (HS.TyForall Nothing [HS.WildCardA Nothing] $ HS.TyForall (Just $ map (\(ABS.U (_, tident)) -> HS.UnkindedVar $ HS.Ident $ headToLower tident) tyvars) [] $
#endif 
          foldr  -- function application is right-associative
          (\ (ABS.FormalPar ptyp _) acc -> tTypeOrTyVar tyvars ptyp `HS.TyFun` acc) 
          (tTypeOrTyVar tyvars fReturnTyp) params)
      , HS.FunBind [HS.Match (mkLoc fpos) (HS.Ident fid) (map (\(ABS.FormalPar _ (ABS.L (_,pid))) -> HS.PVar $ HS.Ident pid) params)
                          Nothing (HS.UnGuardedRhs $
                                         (let ?tyvars = tyvars
                                              ?cname = ""
                                              ?fields = M.empty
                                          in tFunBody body params)
                                   )  Nothing ] ]



-- Classes
tDecl (ABS.DClassParImplements cident@(ABS.U (cpos,clsName)) cparams impls ldecls mInit rdecls) = 

  -- An ADT-record which contains the fields of the class
  HS.DataDecl (mkLoc cpos) HS.DataType [] (HS.Ident clsName) [] 
        [HS.QualConDecl noLoc' [] [] $ HS.RecDecl (HS.Ident clsName) 
                    (foldr (\ ((ABS.L (_,i)), t) acc ->
                      (case t of
                        ABS.TPoly (ABS.U_ (ABS.U (_,"Fut")))  _ -> (([HS.Ident $  i ++ "''" ++ clsName], [ty|[I'.ThreadId]|]) :) -- an extra field holding the threadids
                        _ -> id)
                      (([HS.Ident $  i ++ "'" ++ clsName], tType t): acc) -- TODO: bang if prim type
                     ) [] $ M.toAscList fields)] []

  :
  [HS.TypeSig noLoc' [HS.Ident $ "smart'" ++ clsName]
    (foldr (\ (ABS.FormalPar t _) acc -> tType t `HS.TyFun` acc) (HS.TyCon $ HS.UnQual $ HS.Ident clsName) cparams) 
  ,HS.FunBind [HS.Match noLoc' (HS.Ident $ "smart'" ++ clsName)
    -- the class params serve as input-args to the smart constructor
    (map (\ (ABS.FormalPar _ (ABS.L (_,pid))) -> HS.PVar (HS.Ident $ pid ++ "'this")) cparams) Nothing 
    -- rhs
    (HS.UnGuardedRhs $ runReader (let ?tyvars = []
                                      ?cname = ""  -- it is transformed to pure code, so no need for clsName
                                      ?fields = fields
                                  in tPureExp $ transformFieldBody ldecls) M.empty) Nothing]
  ]
  ++ -- The init'Class function
  [ HS.TypeSig noLoc' [HS.Ident $ "init'" ++ clsName] (HS.TyApp 
                                                      (HS.TyCon $ HS.UnQual $ HS.Ident "Obj'") 
                                                      (HS.TyCon $ HS.UnQual $ HS.Ident clsName) `HS.TyFun` [ty|I'.IO ()|])
  , HS.FunBind [HS.Match (mkLoc cpos) (HS.Ident $ "init'" ++ clsName)
               [[pat|this@(Obj' this' _ thisDC)|]] -- this, the only param
               Nothing 
               (HS.UnGuardedRhs $
                  let runCall = [hs|this <!!> $(HS.Var $ HS.UnQual $ HS.Ident $ "run''" ++ clsName)|]
                  in case mInit of
                    ABS.NoBlock -> if "run" `M.member` aloneMethods
                                  then runCall
                                  else [hs|I'.pure ()|]
                    ABS.JustBlock block -> if "run" `M.member` aloneMethods
                                            then case tMethod block [] fields clsName (M.keys aloneMethods) True of
                                                   HS.Do stms -> HS.Do $ stms ++ [HS.Qualifier runCall]  -- append run statement
                                                   _ -> runCall -- runcall the only rhs
                                            else tMethod block [] fields clsName (M.keys aloneMethods) True
               ) Nothing] ]
    

  ++  -- The direct&indirect instances for interfaces
  concatMap (\ qtyp -> let 
    (prefix, ident) = splitQU qtyp
    Just (SV (Interface directMethods extends) _) = if null prefix
                                                    then M.lookup (SN ident Nothing) ?st
                                                    else M.lookup (SN ident (Just (prefix, False))) ?st 
                                                             <|> M.lookup (SN ident (Just (prefix, True))) ?st 
                      in 
    -- the direct instances
    HS.InstDecl noLoc' Nothing [] [] 
          (HS.UnQual $ HS.Ident $ showQU qtyp ++ "'") -- the interface name
          [HS.TyCon $ HS.UnQual $ HS.Ident $ clsName] -- the class name
          (fmap (\ mname -> let Just (ABS.MethClassBody _typ _ mparams block) = M.lookup mname classMethods
                           in HS.InsDecl (HS.FunBind  [HS.Match noLoc' (HS.Ident mname)
                                                       -- method params
                                                       (map (\ (ABS.FormalPar _ (ABS.L (_,pid))) -> HS.PVar (HS.Ident pid)) mparams ++ [[pat|this@(Obj' this' _ thisDC)|]])
                                                       Nothing 
                                                       (HS.UnGuardedRhs $ tMethod block mparams fields clsName (M.keys aloneMethods) False) Nothing])
                ) (map fst directMethods))
    -- the indirect instances
    : M.foldlWithKey (\ acc (SN n _) indirectMethods ->
                          HS.InstDecl noLoc' Nothing [] [] 
                                (HS.UnQual $ HS.Ident $ n ++ "'") -- the interface name
                                [HS.TyCon $ HS.UnQual $ HS.Ident $ clsName] -- the class name
                                (fmap (\ mname -> let Just (ABS.MethClassBody _typ _ mparams block) = M.lookup mname classMethods
                                                 in HS.InsDecl (HS.FunBind  [HS.Match noLoc' (HS.Ident mname) 
                                                                             -- method params
                                                                             (map (\ (ABS.FormalPar _ (ABS.L (_,pid))) -> HS.PVar (HS.Ident pid)) mparams ++ [[pat|this@(Obj' this' _ thisDC)|]])
                                                                             Nothing 
                                                                             (HS.UnGuardedRhs $ tMethod block mparams fields clsName (M.keys aloneMethods) False) Nothing])
                                      ) (map fst indirectMethods)) : acc
                     ) [] extends
            ) impls

  ++ -- the rest alone, non-interface methods, named as:  method''Class
  concatMap (\ (mname, ABS.MethClassBody retTyp _ mparams block) ->
           [ HS.TypeSig noLoc' [HS.Ident $ mname ++ "''" ++ clsName] $
               foldr HS.TyFun -- function application is right-associative
               (HS.TyApp (HS.TyCon $ HS.UnQual $ HS.Ident "ABS'") (tType retTyp))
               (map (\ (ABS.FormalPar typ _) -> tType typ) mparams ++ [(HS.TyApp 
                                                                       (HS.TyCon $ HS.UnQual $ HS.Ident "Obj'") 
                                                                       (HS.TyCon $ HS.UnQual $ HS.Ident clsName))])
           , HS.FunBind  [HS.Match noLoc' (HS.Ident $ mname ++ "''" ++ clsName)
                         -- method params
                         (map (\ (ABS.FormalPar _ (ABS.L (_,pid))) -> HS.PVar (HS.Ident pid)) mparams ++ [[pat|this@(Obj' this' _ thisDC)|]])
                         Nothing 
                         (HS.UnGuardedRhs $ tMethod block mparams fields clsName (M.keys aloneMethods) False) Nothing]] )
          (M.assocs aloneMethods)

  where
    transformFieldBody :: [ABS.ClassBody] -> ABS.PureExp
    transformFieldBody = foldr (\case
         ABS.MethClassBody _ _ _ _ -> case mInit of
                               ABS.NoBlock -> id -- ignore, TODO: maybe this allows methclassbody to be intertwined with fieldbody
                               ABS.JustBlock _-> error "Second parsing error: Syntactic error, no method declaration accepted here"
         ABS.FieldAssignClassBody t l e -> ABS.ELet (ABS.FormalPar t $ l `appendL` "'this") e
         ABS.FieldClassBody t l@(ABS.L (p,_)) -> case t of
            ABS.TInfer -> errorPos p "Cannot infer type of field which has not been assigned"
            -- it is an unitialized future (abs allows this)
            ABS.TPoly (ABS.U_ (ABS.U (_,"Fut")))  _ -> ABS.ELet (ABS.FormalPar t $ l `appendL` "'this") (ABS.EVar (ABS.L (p,"nullFuture'")))
            -- it may be foreign (to be set to undefined)
            ABS.TPoly qtyp _ -> ABS.ELet (ABS.FormalPar t $ l `appendL` "'this") 
                                                  (let (prefix, ident) = splitQU qtyp
                                                       Just (SV symbolType _) = if null prefix
                                                                                then snd <$> find (\ (SN ident' modul,_) -> ident == ident' && maybe True (not . snd) modul) (M.assocs ?st)
                                                                                else M.lookup (SN ident (Just (prefix, True))) ?st
                                                   in case symbolType of
                                                        Foreign -> ABS.EVar (ABS.L (p,"I'.undefined")) -- [hs|(I'.error "foreign object not initialized")|]
                                                        _ -> errorPos p "A field must be initialised if it is not of a reference type"
                                                  )
            -- it may be an object (to be set to null) or foreign (to be set to undefined)
            ABS.TSimple qtyp -> ABS.ELet (ABS.FormalPar t $ l `appendL` "'this") 
                                  (let (prefix, ident) = splitQU qtyp
                                       Just (SV symbolType _) = if null prefix
                                                                then snd <$> find (\ (SN ident' modul,_) -> ident == ident' && maybe True (not . snd) modul) (M.assocs ?st)
                                                               else M.lookup (SN ident (Just (prefix, True))) ?st 
                                   in case symbolType of
                                        Interface _ _ -> ABS.ELit ABS.LNull -- [hs|$(HS.Var $ HS.UnQual $ HS.Ident $ showQU qtyp) null|]
                                        Foreign -> ABS.EVar (ABS.L (p,"I'.undefined"))-- [hs|(I'.error "foreign object not initialized")|]
                                        _ -> errorPos p "A field must be initialised if it is not of a reference type"
                                  )
                 
         )
         -- the data-constructor of the class applied to the local variables
         (ABS.EParamConstr (ABS.U_ cident) 
          (foldr (\ (fName,fTyp) acc -> case fTyp of
                                          ABS.TPoly (ABS.U_ (ABS.U (p, "Fut"))) _ -> ABS.ESinglConstr (ABS.U_ (ABS.U (p,"Nil"))) : ABS.EVar (fName `appendL` "'this") : acc
                                          _ -> ABS.EVar fName : acc
            ) [] $ M.toAscList fields))

    -- The method names (both implementing & alone methods) of this class mapped to their bodies
    classMethods :: M.Map String ABS.ClassBody
    classMethods = M.fromList $ mapMaybe (\case 
                                     m@(ABS.MethClassBody _ (ABS.L (_,ident)) _ _) -> Just (ident,m)
                                     _ -> Nothing)
                                    (case mInit of
                                       ABS.NoBlock -> ldecls
                                       ABS.JustBlock _ -> rdecls)

    -- All (class-params and declared) fields of this class
    fields :: ScopeLVL -- order matters, because the fields are indexed
    fields = M.fromList $ map (\ (ABS.FormalPar t i) -> (i,t)) cparams ++ mapMaybe (\case
                                                                               ABS.FieldClassBody t i -> Just (i,t)
                                                                               ABS.FieldAssignClassBody t i _ -> Just (i,t)
                                                                               ABS.MethClassBody _ _ _ _ -> Nothing
                                                                              ) ldecls

    aloneMethods :: M.Map String ABS.ClassBody
    aloneMethods = M.filterWithKey (\ m _ -> m `notElem` toImplementMethods) classMethods
        where
          toImplementMethods :: [String]
          toImplementMethods = concatMap (\ (SV (Interface dmethods extends) _) -> map fst $ concat $ dmethods : M.elems extends) $
                         M.elems $ M.filterWithKey (\ (SN i _) _ -> i `elem` map (snd . splitQU) impls) ?st


-- Type synonyms with variables
tDecl (ABS.DTypePoly (ABS.U (tpos,tid)) tyvars typ) = [HS.TypeDecl (mkLoc tpos) (HS.Ident tid) 
                                                                 (map (\ (ABS.U (_,varid)) -> 
                                                                           HS.UnkindedVar $ HS.Ident $ headToLower varid)
                                                                  tyvars)
                                                                 (tTypeOrTyVar tyvars typ)
                                                          ]

-- Datatypes
tDecl (ABS.DDataPoly (ABS.U (dpos,tid)) tyvars constrs) =  HS.DataDecl (mkLoc dpos) HS.DataType [] (HS.Ident tid) 

          -- Type Variables
          (map (\ (ABS.U (_,varid)) -> HS.UnkindedVar $ HS.Ident $ headToLower varid) tyvars)

          -- Data Constructors
          (map (\case
                ABS.SinglConstrIdent (ABS.U (_,cid)) -> HS.QualConDecl noLoc' [] [] (HS.ConDecl (HS.Ident cid) []) 
                ABS.ParamConstrIdent (ABS.U (_,cid)) args -> HS.QualConDecl noLoc' [] [] (HS.ConDecl (HS.Ident cid) (map (HS.TyBang HS.BangedTy . tTypeOrTyVar tyvars . typOfConstrType) args))) constrs) -- TODO: maybe only allow Banged Int,Double,... like the class-datatype

          -- Deriving
          (if hasInterfForeign constrs
           then [(HS.Qual (HS.ModuleName "I'") $ HS.Ident "Eq", []), (HS.Qual (HS.ModuleName "I'") $ HS.Ident "Show", [])]
           else [(HS.Qual (HS.ModuleName "I'") $ HS.Ident "Eq", []), (HS.Qual (HS.ModuleName "I'") $ HS.Ident "Ord", []),  (HS.Qual (HS.ModuleName "I'") $ HS.Ident "Show", [])])
          -- Generate a GeniFunctor if it is a polymorphic datatype
          : (if null tyvars 
             then [] 
             else [HS.SpliceDecl noLoc' [hs|return []|]
                  ,HS.PatBind noLoc' (HS.PVar $ HS.Ident $ "fmap'" ++ tid) (HS.UnGuardedRhs $ HS.SpliceExp $ HS.ParenSplice $ [hs|I'.genFmap|] `HS.App` HS.TypQuote (HS.UnQual $ HS.Ident tid)) Nothing])
          -- Extra record-accessor functions
          ++ map (\ (ABS.L (_,fname), consname, idx, len) ->  
                     HS.FunBind [HS.Match noLoc' (HS.Ident fname) [HS.PApp (HS.UnQual (HS.Ident consname)) (replicate idx HS.PWildCard ++ [HS.PVar (HS.Ident "a")] ++ replicate (len - idx - 1) HS.PWildCard)] Nothing (HS.UnGuardedRhs (HS.Var (HS.UnQual (HS.Ident "a")))) Nothing,
                                 HS.Match noLoc' (HS.Ident fname) [HS.PWildCard] Nothing (HS.UnGuardedRhs [hs|I'.throw (RecSelError (concatenate "Data constructor does not have accessor " $(HS.Lit $ HS.String fname)))|]) Nothing
                     ]) (
             concatMap (\case
               ABS.SinglConstrIdent _ -> []
               ABS.ParamConstrIdent (ABS.U (_,cid)) args -> -- taking the indices of fields
                                         let len = length args
                                         in
                                            foldl (\ acc (field, idx) ->  case field of
                                                                            ABS.EmptyConstrType _ -> acc
                                                                            ABS.RecordConstrType _ fid -> (fid, cid, idx, len):acc) [] (zip args [0..])
              ) constrs )
    where
      hasInterfForeign :: [ABS.ConstrIdent] -> Bool
      hasInterfForeign [] = False
      hasInterfForeign (ABS.SinglConstrIdent _ : constrs') = hasInterfForeign constrs' -- ignore singleconstrident
      hasInterfForeign (ABS.ParamConstrIdent _ params : constrs') =  
       let monomorphicTypes = filter (\case 
                                  ABS.U_ u -> u `notElem` tyvars 
                                  _ -> True) $ collectTypes params
       in foldl (\ acc qu ->
        let (prefix, ident) = splitQU qu
        in acc || isJust (if null prefix
                          then M.lookup (SN ident Nothing) ?st
                          else M.lookup (SN ident (Just (prefix, False))) ?st <|> M.lookup (SN ident (Just (prefix, True))) ?st)
        ) False monomorphicTypes || hasInterfForeign constrs' 
        
      collectTypes :: [ABS.ConstrType] -> [ABS.QU]
      collectTypes = concatMap (\case
                                  ABS.EmptyConstrType t -> collectType t
                                  ABS.RecordConstrType t _ -> collectType t)
      collectType :: ABS.T -> [ABS.QU]
      collectType (ABS.TPoly _ ts) = concatMap collectType ts
      collectType (ABS.TSimple qu) = [qu]
      collectType _ = []

      typOfConstrType :: ABS.ConstrType -> ABS.T
      typOfConstrType (ABS.EmptyConstrType typ) = typ
      typOfConstrType (ABS.RecordConstrType typ _) = typ

         
-- Exception datatypes
tDecl (ABS.DException constr) =
  -- 1) a data MyException = MyException(args)
  [ HS.DataDecl (mkLoc epos) HS.DataType [] (HS.Ident cid) [] 
    -- one sole constructor with the same name as the exception name
    [HS.QualConDecl noLoc' [] [] 
      (HS.ConDecl (HS.Ident cid)
        (map (HS.TyBang HS.BangedTy . tType . typOfConstrType) cargs))]
    -- two deriving for exception datatypes Show and Typeable (TODO: Eq for ABS) (GHC>=7.10 by default auto-derives Typeable if needed)
    [(HS.Qual (HS.ModuleName "I'") (HS.Ident "Show"), [])]
  -- 2) a instance Exception MyException
  , HS.InstDecl noLoc' Nothing [] [] (HS.Qual (HS.ModuleName "I'") $ HS.Ident $ "Exception") [HS.TyCon $ HS.UnQual $ HS.Ident cid] 
      [ HS.InsDecl [dec|toException = absExceptionToException'|]
      , HS.InsDecl [dec|fromException = absExceptionFromException'|]
      ]
  ]
  -- TODO: allow or disallow record-accessor functions for exception, because it requires type-safe casting
  where ((epos,cid), cargs) = case constr of
                            ABS.SinglConstrIdent (ABS.U tid) -> (tid, [])
                            ABS.ParamConstrIdent (ABS.U tid) args -> (tid, args)                                       
        typOfConstrType (ABS.EmptyConstrType typ) = typ
        typOfConstrType (ABS.RecordConstrType typ _) = typ


-- Interfaces
tDecl (ABS.DExtends (ABS.U (ipos,tname)) extends ms) = HS.ClassDecl (mkLoc ipos) 
        (map (\ qtyp -> HS.ClassA (HS.UnQual $ HS.Ident $ showQU qtyp ++ "'") [HS.TyVar (HS.Ident "a")]) extends) -- super-interfaces
        (HS.Ident $ tname ++ "'") -- name of interface
        [HS.UnkindedVar (HS.Ident "a")] -- all interfaces have kind * -> *
        []
        (map tMethSig ms)
      : -- Existential Wrapper
      HS.DataDecl noLoc' HS.DataType [] (HS.Ident tname) [] [HS.QualConDecl noLoc' [HS.UnkindedVar $ HS.Ident "a"] [HS.ClassA (HS.UnQual $ HS.Ident $ tname ++ "'") [HS.TyVar (HS.Ident "a")]] (HS.ConDecl (HS.Ident tname) [HS.TyApp (HS.TyCon $ HS.UnQual $ HS.Ident "Obj'") (HS.TyVar $ HS.Ident "a")])] []
      : -- Show instance for the wrapper
      HS.InstDecl noLoc' Nothing [] [] (HS.Qual (HS.ModuleName "I'") $ HS.Ident "Show") [HS.TyCon $ HS.UnQual $ HS.Ident $ tname]
            [HS.InsDecl (HS.FunBind  [HS.Match noLoc' (HS.Ident "show") [HS.PWildCard] Nothing (HS.UnGuardedRhs $ HS.Lit $ HS.String tname) Nothing])]
      : -- Eq instance for the wrapper
      HS.InstDecl noLoc' Nothing [] [] (HS.Qual (HS.ModuleName "I'") $ HS.Ident  "Eq") [HS.TyCon $ HS.UnQual $ HS.Ident tname]
         [HS.InsDecl $ HS.FunBind [HS.Match noLoc' (HS.Symbol "==") 
                                   [HS.PApp (HS.UnQual $ HS.Ident tname) [HS.PApp (HS.UnQual $ HS.Ident "Obj'") [HS.PVar $ HS.Ident "ref1'", HS.PWildCard, HS.PWildCard]],
                                    HS.PApp (HS.UnQual $ HS.Ident tname) [HS.PApp (HS.UnQual $ HS.Ident "Obj'") [HS.PVar $ HS.Ident "ref2'", HS.PWildCard, HS.PWildCard]]]
                                   Nothing (HS.UnGuardedRhs [hs|ref1' == I'.unsafeCoerce ref2'|]) Nothing]]

       -- null class is an instance of any interface
       : HS.InstDecl noLoc' Nothing [] [] (HS.UnQual $ HS.Ident $ tname ++ "'") [HS.TyCon $ HS.UnQual $ HS.Ident "Null'"] 
             (map (\ (ABS.MethSig _ _ (ABS.L (_,mid)) _) -> 
                       HS.InsDecl [dec|__mid__ = I'.undefined|] ) ms)


      : -- Sub instance for unwrapped this & null
      HS.InstDecl noLoc' Nothing []
            [HS.ClassA (HS.UnQual $ HS.Ident (tname ++ "'")) [HS.TyVar $ HS.Ident "a"]] -- context
            (HS.UnQual $ HS.Ident "Sub'")  -- instance (I1' a) => Sub (Obj' a) I1
            [ HS.TyApp (HS.TyCon $ HS.UnQual $ HS.Ident "Obj'") (HS.TyVar $ HS.Ident "a")
            , HS.TyCon $ HS.UnQual $ HS.Ident $ tname]
            [   -- the upcasting method
                -- is wrapping with the constructor
                HS.InsDecl $ HS.FunBind $ [HS.Match noLoc' (HS.Ident "up'") [] Nothing 
                                                 (HS.UnGuardedRhs $ (HS.Con $ HS.UnQual $ HS.Ident tname)
                                                 ) Nothing] ]

      : -- Sub instances of all direct AND indirect supertypes
      generateSubForAllSupers

    where
    -- method_signature :: args -> Obj a (THIS) -> (res -> ABS ()) -> ABS ()
    tMethSig :: ABS.MethSig -> HS.ClassDecl
    tMethSig (ABS.MethSig _ retTyp (ABS.L (mpos,mname)) params) = 
        if mname == "run" && ((case retTyp of
                              ABS.TSimple (ABS.U_ (ABS.U (_, "Unit"))) -> False
                              _ -> True) || not (null params))
        then errorPos mpos "run should have zero parameters and return type Unit"
        else HS.ClsDecl $ HS.TypeSig (mkLoc mpos) [HS.Ident mname] $
               foldr  HS.TyFun -- function application is right-associative
                 (HS.TyApp (HS.TyCon $ HS.UnQual $ HS.Ident "ABS'") (tType retTyp))
                 (map (\ (ABS.FormalPar typ _) -> tType typ) params ++ [(HS.TyApp (HS.TyCon $ HS.UnQual $ HS.Ident "Obj'") (HS.TyVar $ HS.Ident "a"))]) -- last param is this

    generateSubForAllSupers :: (?st::SymbolTable) => [HS.Decl]
    generateSubForAllSupers = case M.lookup (SN tname Nothing) ?st of
                     Just (SV (Interface _ all_extends) _) -> map 
                      (\ (SN sup _) -> HS.InstDecl noLoc' Nothing [] []
                       (HS.UnQual $ HS.Ident "Sub'")
                       [HS.TyCon $ HS.UnQual $ HS.Ident tname, HS.TyCon $ HS.UnQual $ HS.Ident sup] -- instance Sub SubInterf SupInterf
                       [   -- the upcasting method is unwrapping and wrapping the data constructors
                          HS.InsDecl $ HS.FunBind $ [HS.Match noLoc' (HS.Ident "up'") [HS.PApp (HS.UnQual $ HS.Ident tname) [HS.PVar $ HS.Ident "x'"]] Nothing 
                                                           (HS.UnGuardedRhs $ HS.App (HS.Con $ HS.UnQual $ HS.Ident sup)
                                                                  (HS.Var $ HS.UnQual $ HS.Ident "x'")) Nothing]
                       ])
                      (M.keys all_extends)
                     _ -> error "development error at firstpass"
                    
    
