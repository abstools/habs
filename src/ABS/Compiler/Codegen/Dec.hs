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
import qualified Language.Haskell.Exts.Simple.Syntax as HS
import Data.List (find)

import Control.Exception (assert)
#define total assert False (error "This error should not happen. Contact developers")


-- Datatypes
tDataInterfDecl :: (?absFileName::String, ?st::SymbolTable) => ABS.Decl -> [HS.Decl]
tDataInterfDecl (ABS.DData tid constrs) =  tDataInterfDecl (ABS.DDataPoly tid [] constrs) -- Normalization: just parametric datatype with empty list of type variables
tDataInterfDecl (ABS.DDataPoly (ABS.U (dpos,tid)) tyvars constrs) =  HS.DataDecl HS.DataType Nothing
          -- Name and type Variables
          (foldl (\ acc (ABS.U (_,varid))-> HS.DHApp acc $ HS.UnkindedVar $ HS.Ident $ headToLower varid) (HS.DHead $ HS.Ident tid) tyvars)
          
          -- Data Constructors
          (map (\case
                ABS.SinglConstrIdent (ABS.U (_,cid)) -> HS.QualConDecl Nothing Nothing (HS.ConDecl (HS.Ident cid) []) 
                ABS.ParamConstrIdent (ABS.U (_,cid)) args -> HS.QualConDecl Nothing Nothing (HS.ConDecl (HS.Ident cid) (map (HS.TyBang HS.BangedTy HS.NoUnpack . tTypeOrTyVar tyvars . typOfConstrType) args))) constrs) -- TODO: maybe only allow Banged Int,Double,... like the class-datatype

          -- Deriving
          (Just $ HS.Deriving $ fmap (HS.IRule Nothing Nothing . HS.IHCon . HS.Qual (HS.ModuleName "I'") . HS.Ident )
           (if hasInterfForeign constrs then ["Eq", "Show"] else ["Eq", "Ord", "Show"]))
          -- Extra record-accessor functions
          : map (\ (ABS.L (_,fname), consname, idx, len) ->  
                     HS.FunBind [HS.Match (HS.Ident fname) [HS.PApp (HS.UnQual (HS.Ident consname)) (replicate idx HS.PWildCard ++ [HS.PVar (HS.Ident "a")] ++ replicate (len - idx - 1) HS.PWildCard)] (HS.UnGuardedRhs (HS.Var (HS.UnQual (HS.Ident "a")))) Nothing,
                                 HS.Match (HS.Ident fname) [HS.PWildCard] (HS.UnGuardedRhs [hs|I'.throw (RecSelError (concatenate "Data constructor does not have accessor " $(HS.Lit $ HS.String fname)))|]) Nothing
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


tDataInterfDecl (ABS.DInterf tid ms) = tDataInterfDecl (ABS.DExtends tid [] ms) 

-- Interfaces
tDataInterfDecl (ABS.DExtends (ABS.U (ipos,tname)) extends ms) = HS.ClassDecl 
        (Just $ HS.CxTuple $ map (\ qtyp -> HS.ClassA (HS.UnQual $ HS.Ident $ showQU qtyp ++ "'") [HS.TyVar (HS.Ident "a")]) extends) -- super-interfaces
        (HS.DHead (HS.Ident $ tname ++ "'") `HS.DHApp` HS.UnkindedVar (HS.Ident "a")) -- all interfaces have kind * -> *
        []
        (Just $ map tMethSig ms)
      : -- Existential Wrapper
      HS.DataDecl HS.DataType Nothing (HS.DHead $ HS.Ident tname) [HS.QualConDecl (Just [HS.UnkindedVar $ HS.Ident "a"]) (Just $ HS.CxSingle $ HS.ClassA (HS.UnQual $ HS.Ident $ tname ++ "'") [HS.TyVar (HS.Ident "a")]) (HS.ConDecl (HS.Ident tname) [HS.TyApp (HS.TyCon $ HS.UnQual $ HS.Ident "Obj'") (HS.TyVar $ HS.Ident "a")])] Nothing
      : -- Show instance for the wrapper
      HS.InstDecl Nothing (HS.IRule Nothing Nothing $ HS.IHCon (HS.Qual (HS.ModuleName "I'") $ HS.Ident "Show") `HS.IHApp` HS.TyCon (HS.UnQual $ HS.Ident $ tname))
            (Just [HS.InsDecl (HS.FunBind  [HS.Match (HS.Ident "show") [HS.PWildCard] (HS.UnGuardedRhs $ HS.Lit $ HS.String tname) Nothing])])
      : -- Eq instance for the wrapper
      HS.InstDecl Nothing (HS.IRule Nothing Nothing $ HS.IHCon (HS.Qual (HS.ModuleName "I'") $ HS.Ident "Eq") `HS.IHApp` HS.TyCon (HS.UnQual $ HS.Ident $ tname))
         (Just [HS.InsDecl $ HS.FunBind [HS.Match (HS.Symbol "==") 
                                   [HS.PApp (HS.UnQual $ HS.Ident tname) [HS.PApp (HS.UnQual $ HS.Ident "Obj'") [HS.PVar $ HS.Ident "ref1'", HS.PWildCard, HS.PWildCard]],
                                    HS.PApp (HS.UnQual $ HS.Ident tname) [HS.PApp (HS.UnQual $ HS.Ident "Obj'") [HS.PVar $ HS.Ident "ref2'", HS.PWildCard, HS.PWildCard]]]
                                    (HS.UnGuardedRhs [hs|ref1' == I'.unsafeCoerce ref2'|]) Nothing]])

       -- null class is an instance of any interface
       : HS.InstDecl Nothing (HS.IRule Nothing Nothing $ HS.IHCon (HS.UnQual $ HS.Ident $ tname ++ "'") `HS.IHApp` (HS.TyCon $ HS.UnQual $ HS.Ident "Null'"))
             (Just $ map (\ (ABS.MethSig _ _ (ABS.L (_,mid)) _) -> 
                       HS.InsDecl [dec|__mid__ = I'.undefined|] ) ms)


      : -- Sub instance for unwrapped this & null -- instance (I1' a) => Sub (Obj' a) I1
      HS.InstDecl Nothing (HS.IRule Nothing 
            (Just $ HS.CxSingle $ HS.ClassA (HS.UnQual $ HS.Ident (tname ++ "'")) [HS.TyVar $ HS.Ident "a"]) -- context
            (HS.IHCon (HS.UnQual $ HS.Ident "Sub'")
              `HS.IHApp`  
              (HS.TyParen $ HS.TyApp (HS.TyCon $ HS.UnQual $ HS.Ident "Obj'") (HS.TyVar $ HS.Ident "a"))
              `HS.IHApp`
              (HS.TyCon $ HS.UnQual $ HS.Ident $ tname)))
            (Just [   -- the upcasting method
                -- is wrapping with the constructor
                HS.InsDecl $ HS.FunBind $ [HS.Match (HS.Ident "up'") [] 
                                                 (HS.UnGuardedRhs $ (HS.Con $ HS.UnQual $ HS.Ident tname)
                                                 ) Nothing] ])

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
        else HS.ClsDecl $ HS.TypeSig [HS.Ident mname] $
               foldr  HS.TyFun -- function application is right-associative
                 (HS.TyApp (HS.TyCon $ HS.UnQual $ HS.Ident "ABS'") (tType retTyp))
                 (map (\ (ABS.FormalPar typ _) -> tType typ) params ++ [(HS.TyApp (HS.TyCon $ HS.UnQual $ HS.Ident "Obj'") (HS.TyVar $ HS.Ident "a"))]) -- last param is this

    generateSubForAllSupers :: (?st::SymbolTable) => [HS.Decl]
    generateSubForAllSupers = case M.lookup (SN tname Nothing) ?st of
                     Just (SV (Interface _ all_extends) _) -> map 
                      (\ (SN sup _) -> HS.InstDecl Nothing (HS.IRule Nothing Nothing $ HS.IHCon (HS.UnQual $ HS.Ident "Sub'") `HS.IHApp` HS.TyCon (HS.UnQual $ HS.Ident tname) `HS.IHApp` HS.TyCon (HS.UnQual $ HS.Ident sup)) -- instance Sub SubInterf SupInterf
                       (Just [   -- the upcasting method is unwrapping and wrapping the data constructors
                          HS.InsDecl $ HS.FunBind $ [HS.Match (HS.Ident "up'") [HS.PApp (HS.UnQual $ HS.Ident tname) [HS.PVar $ HS.Ident "x'"]] 
                                                           (HS.UnGuardedRhs $ HS.App (HS.Con $ HS.UnQual $ HS.Ident sup)
                                                                  (HS.Var $ HS.UnQual $ HS.Ident "x'")) Nothing]
                       ]))
                      (M.keys all_extends)
                     _ -> error "development error at firstpass"

tDataInterfDecl _ = total


tRestDecl :: (?absFileName::String, ?st::SymbolTable) => ABS.Decl -> [HS.Decl]

-- Normalizations
tRestDecl (ABS.DFun fReturnTyp fid params body) = tRestDecl (ABS.DFunPoly fReturnTyp fid [] params body) -- normalize to no type variables
tRestDecl (ABS.DType tid typ) = tRestDecl (ABS.DTypePoly tid [] typ) -- type synonym with no type variables
tRestDecl (ABS.DClass tident fdecls maybeBlock mdecls) = tRestDecl (ABS.DClassParImplements tident [] [] fdecls maybeBlock mdecls)
tRestDecl (ABS.DClassPar tident params fdecls maybeBlock mdecls) = tRestDecl (ABS.DClassParImplements tident params [] fdecls maybeBlock mdecls)
tRestDecl (ABS.DClassImplements tident imps fdecls maybeBlock mdecls) = tRestDecl (ABS.DClassParImplements tident [] imps fdecls maybeBlock mdecls)


-- Functions
tRestDecl (ABS.DFunPoly fReturnTyp (ABS.L (fpos,fid)) tyvars params body) = [
        HS.TypeSig [HS.Ident fid] (HS.TyForall (Just $ map (\(ABS.U (_, tident)) -> HS.UnkindedVar $ HS.Ident $ headToLower tident) tyvars) (Just $ HS.CxSingle $ HS.WildCardA Nothing) $
          foldr  -- function application is right-associative
          (\ (ABS.FormalPar ptyp _) acc -> tTypeOrTyVar tyvars ptyp `HS.TyFun` acc) 
          (tTypeOrTyVar tyvars fReturnTyp) params)
      , HS.FunBind [HS.Match (HS.Ident fid) (map (\(ABS.FormalPar _ (ABS.L (_,pid))) -> HS.PVar $ HS.Ident pid) params)
                           (HS.UnGuardedRhs $
                                         (let ?cname = ""
                                              ?fields = M.empty
                                          in tFunBody body tyvars params fReturnTyp)
                                   )  Nothing ] ]



-- Classes
tRestDecl (ABS.DClassParImplements cident@(ABS.U (cpos,clsName)) cparams impls ldecls mInit rdecls) = 

  -- An ADT-record which contains the fields of the class
  HS.DataDecl HS.DataType Nothing (HS.DHead $ HS.Ident clsName)
        [HS.QualConDecl Nothing Nothing $ HS.RecDecl (HS.Ident clsName) 
                    (foldr (\ ((ABS.L (_,i)), t) acc ->
                      (case t of
                        ABS.TPoly (ABS.U_ (ABS.U (_,"Fut")))  _ -> (HS.FieldDecl [HS.Ident $  i ++ "''" ++ clsName] [ty|[I'.ThreadId]|] :) -- an extra field holding the threadids
                        _ -> id)
                      (HS.FieldDecl [HS.Ident $  i ++ "'" ++ clsName] (tType t): acc) -- TODO: bang if prim type
                     ) [] $ M.toAscList fields)] Nothing

  :
  [HS.TypeSig [HS.Ident $ "smart'" ++ clsName]
    (foldr (\ (ABS.FormalPar t _) acc -> tType t `HS.TyFun` acc) (HS.TyCon $ HS.UnQual $ HS.Ident clsName) cparams) 
  ,HS.FunBind [HS.Match (HS.Ident $ "smart'" ++ clsName)
    -- the class params serve as input-args to the smart constructor
    (map (\ (ABS.FormalPar _ (ABS.L (_,pid))) -> HS.PVar (HS.Ident $ pid ++ "'this")) cparams) 
    -- rhs
    (HS.UnGuardedRhs $ fst $ runReader (let ?cname = ""  -- it is transformed to pure code, so no need for clsName
                                            ?fields = fields
                                        in tPureExp $ transformFieldBody ldecls) M.empty) Nothing]
  ]
  ++ -- The init'Class function
  [ HS.TypeSig [HS.Ident $ "init'" ++ clsName] (HS.TyApp 
                                                      (HS.TyCon $ HS.UnQual $ HS.Ident "Obj'") 
                                                      (HS.TyCon $ HS.UnQual $ HS.Ident clsName) `HS.TyFun` [ty|I'.IO ()|])
  , HS.FunBind [HS.Match (HS.Ident $ "init'" ++ clsName)
               [[pat|this@(Obj' this' _ thisDC)|]] -- this, the only param
               (HS.UnGuardedRhs $
                  let runCall = [hs|this <!!> $(HS.Var $ HS.UnQual $ HS.Ident $ "run''" ++ clsName)|]
                  in case mInit of
                    ABS.NoBlock -> if "run" `M.member` aloneMethods
                                  then runCall
                                  else [hs|I'.pure ()|]
                    ABS.JustBlock block -> if "run" `M.member` aloneMethods
                                            then case tMethod block [] fields clsName (M.keys aloneMethods) True ABS.TInfer of
                                                   HS.Do stms -> HS.Do $ stms ++ [HS.Qualifier runCall]  -- append run statement
                                                   _ -> runCall -- runcall the only rhs
                                            else tMethod block [] fields clsName (M.keys aloneMethods) True ABS.TInfer
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
    HS.InstDecl Nothing (HS.IRule Nothing Nothing $ HS.IHCon (HS.UnQual $ HS.Ident $ showQU qtyp ++ "'") `HS.IHApp` HS.TyCon (HS.UnQual $ HS.Ident $ clsName))
          (Just $ fmap (\ mname -> let Just (ABS.MethClassBody retTyp _ mparams block) = M.lookup mname classMethods
                           in HS.InsDecl (HS.FunBind  [HS.Match (HS.Ident mname)
                                                       -- method params
                                                       (map (\ (ABS.FormalPar _ (ABS.L (_,pid))) -> HS.PVar (HS.Ident pid)) mparams ++ [[pat|this@(Obj' this' _ thisDC)|]])
                                                       (HS.UnGuardedRhs $ tMethod block mparams fields clsName (M.keys aloneMethods) False retTyp) Nothing])
                ) (map fst directMethods))
    -- the indirect instances
    : M.foldlWithKey (\ acc (SN n _) indirectMethods ->
                          HS.InstDecl Nothing (HS.IRule Nothing Nothing $ HS.IHCon (HS.UnQual $ HS.Ident $ n ++ "'") `HS.IHApp` HS.TyCon (HS.UnQual $ HS.Ident $ clsName))
                                (Just $ fmap (\ mname -> let Just (ABS.MethClassBody retTyp _ mparams block) = M.lookup mname classMethods
                                                 in HS.InsDecl (HS.FunBind  [HS.Match (HS.Ident mname) 
                                                                             -- method params
                                                                             (map (\ (ABS.FormalPar _ (ABS.L (_,pid))) -> HS.PVar (HS.Ident pid)) mparams ++ [[pat|this@(Obj' this' _ thisDC)|]])
                                                                             (HS.UnGuardedRhs $ tMethod block mparams fields clsName (M.keys aloneMethods) False retTyp) Nothing])
                                      ) (map fst indirectMethods)) : acc
                     ) [] extends
            ) impls

  ++ -- the rest alone, non-interface methods, named as:  method''Class
  concatMap (\ (mname, ABS.MethClassBody retTyp _ mparams block) ->
           [ HS.TypeSig [HS.Ident $ mname ++ "''" ++ clsName] $
               foldr HS.TyFun -- function application is right-associative
               (HS.TyApp (HS.TyCon $ HS.UnQual $ HS.Ident "ABS'") (tType retTyp))
               (map (\ (ABS.FormalPar typ _) -> tType typ) mparams ++ [(HS.TyApp 
                                                                       (HS.TyCon $ HS.UnQual $ HS.Ident "Obj'") 
                                                                       (HS.TyCon $ HS.UnQual $ HS.Ident clsName))])
           , HS.FunBind  [HS.Match (HS.Ident $ mname ++ "''" ++ clsName)
                         -- method params
                         (map (\ (ABS.FormalPar _ (ABS.L (_,pid))) -> HS.PVar (HS.Ident pid)) mparams ++ [[pat|this@(Obj' this' _ thisDC)|]])
                         (HS.UnGuardedRhs $ tMethod block mparams fields clsName (M.keys aloneMethods) False retTyp) Nothing]] )
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
tRestDecl (ABS.DTypePoly (ABS.U (tpos,tid)) tyvars typ) = 
  [HS.TypeDecl (foldl (\ acc (ABS.U (_,varid)) -> HS.DHApp acc $ HS.UnkindedVar $ HS.Ident $ headToLower varid) (HS.DHead $ HS.Ident tid) tyvars) (tTypeOrTyVar tyvars typ)]

         
-- Exception datatypes
tRestDecl (ABS.DException constr) =
  -- 1) a data MyException = MyException(args)
  [ HS.DataDecl HS.DataType Nothing (HS.DHead $ HS.Ident cid)
    -- one sole constructor with the same name as the exception name
    [HS.QualConDecl Nothing Nothing
      (HS.ConDecl (HS.Ident cid)
        (map (HS.TyBang HS.BangedTy HS.NoUnpack . tType . typOfConstrType) cargs))]
    -- two deriving for exception datatypes Show and Typeable (TODO: Eq for ABS) (GHC>=7.10 by default auto-derives Typeable if needed)
    (Just $ HS.Deriving [HS.IRule Nothing Nothing $ HS.IHCon $ HS.Qual (HS.ModuleName "I'") $ HS.Ident "Show"])
  -- 2) a instance Exception MyException
  , HS.InstDecl Nothing (HS.IRule Nothing Nothing $ HS.IHCon (HS.Qual (HS.ModuleName "I'") $ HS.Ident $ "Exception") `HS.IHApp` HS.TyCon (HS.UnQual $ HS.Ident cid))
      (Just [ HS.InsDecl [dec|toException = absExceptionToException'|]
      , HS.InsDecl [dec|fromException = absExceptionFromException'|]
      ])
  ]
  -- TODO: allow or disallow record-accessor functions for exception, because it requires type-safe casting
  where ((epos,cid), cargs) = case constr of
                            ABS.SinglConstrIdent (ABS.U tid) -> (tid, [])
                            ABS.ParamConstrIdent (ABS.U tid) args -> (tid, args)                                       
        typOfConstrType (ABS.EmptyConstrType typ) = typ
        typOfConstrType (ABS.RecordConstrType typ _) = typ

    
tRestDecl _ = total