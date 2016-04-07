{-# LANGUAGE ImplicitParams, QuasiQuotes, TemplateHaskell, LambdaCase #-}
module ABS.Compiler.Codegen.Dec where

import ABS.Compiler.Utils
import ABS.Compiler.Firstpass.Base
import ABS.Compiler.Codegen.Typ
import ABS.Compiler.Codegen.Exp
import ABS.Compiler.Codegen.Stm (tMethod)
import Language.Haskell.Exts.SrcLoc (noLoc)
import Language.Haskell.Exts.QQ (hs, dec)

import Control.Applicative ((<|>))
import Control.Monad.Trans.Reader (runReader)
import Data.Foldable (foldlM)
import Data.Maybe (mapMaybe)
import qualified Data.Map as M
import qualified ABS.AST as ABS
import qualified Language.Haskell.Exts.Syntax as HS

tDecl :: (?st :: SymbolTable) => ABS.Decl -> [HS.Decl]

-- Normalizations
tDecl (ABS.FunDecl fReturnTyp fid params body) = tDecl (ABS.FunParDecl fReturnTyp fid [] params body) -- normalize to no type variables
tDecl (ABS.ClassDecl tident fdecls maybeBlock mdecls) = tDecl (ABS.ClassParamImplements tident [] [] fdecls maybeBlock mdecls)
tDecl (ABS.ClassParamDecl tident params fdecls maybeBlock mdecls) = tDecl (ABS.ClassParamImplements tident params [] fdecls maybeBlock mdecls)
tDecl (ABS.ClassImplements tident imps fdecls maybeBlock mdecls) = tDecl (ABS.ClassParamImplements tident [] imps fdecls maybeBlock mdecls)
tDecl (ABS.DataDecl tid constrs) =  tDecl (ABS.DataParDecl tid [] constrs) -- just parametric datatype with empty list of type variables
tDecl (ABS.InterfDecl tid ms) = tDecl (ABS.ExtendsDecl tid [] ms) 


-- Functions
tDecl (ABS.FunParDecl fReturnTyp (ABS.LIdent (_,fid)) tyvars params body) = [
        HS.FunBind [HS.Match noLoc (HS.Ident fid) (map (\ (ABS.Par ptyp (ABS.LIdent (_,pid))) -> 
                                                            (\ pat -> case ptyp of
                                                                       ABS.TUnderscore -> pat
                                                                       _ -> HS.PatTypeSig noLoc pat (tTypeOrTyVar tyvars ptyp) -- wrap with an explicit type annotation
                                                            ) (HS.PVar (HS.Ident pid))) params)
                          Nothing (HS.UnGuardedRhs $
                                         (\ exp -> case fReturnTyp of
                                                    ABS.TUnderscore -> exp -- infer the return type
                                                    _ -> HS.ExpTypeSig noLoc exp (tTypeOrTyVar tyvars fReturnTyp)) -- wrap the return exp with an explicit type annotation
                                         (let ?tyvars = tyvars
                                              ?cname = []
                                              ?fields = M.empty
                                          in tFunBody body params)
                                   )  Nothing ] ]



-- Classes
tDecl (ABS.ClassParamImplements (ABS.UIdent (_,clsName)) cparams impls ldecls mInit rdecls) = 

  -- An ADT-record which contains the fields of the class
  HS.DataDecl noLoc HS.DataType [] (HS.Ident clsName) [] 
        [HS.QualConDecl noLoc [] [] $ HS.RecDecl (HS.Ident clsName) (map (\ ((ABS.LIdent (_,i)), t) -> ([HS.Ident $  i ++ "'" ++ clsName], 
                                                                                                                tType t -- TODO: bang if prim type
                                                                                                      )) (M.toAscList fields))]  []

  : -- A smart-constructor for pure fields
  HS.FunBind [HS.Match noLoc (HS.Ident $ "smart'" ++ clsName)
    -- the class params serve as input-args to the smart constructor
    (map (\ (ABS.Par _ (ABS.LIdent (_,pid))) -> HS.PVar (HS.Ident pid)) cparams) Nothing 
    -- rhs
    (HS.UnGuardedRhs $ HS.RecConstr (HS.UnQual $ HS.Ident clsName) $
     let ?tyvars = []
         ?cname = clsName
         ?fields = fields
     in runReader (foldlM (\ acc -> \case
                           
                   -- Field f = val;
                   ABS.FieldAssignClassBody _t (ABS.LIdent (_, fid)) pexp -> do
                      texp <- tPureExp pexp
                      return $ HS.FieldUpdate (HS.UnQual $ HS.Ident $ fid ++ "'" ++ clsName) texp : acc

                   -- Field f;
                   ABS.FieldClassBody t (ABS.LIdent (p,fid)) ->  case t of
                               -- it is an unitialized future (abs allows this)
                               ABS.TGen (ABS.QTyp [ABS.QTypeSegmen (ABS.UIdent (_,"Fut"))])  _ -> 
                                   return $ HS.FieldUpdate (HS.UnQual $ HS.Ident $ fid ++ "'" ++ clsName) [hs| emptyFuture |] : acc
                               -- it may be an object (to be set to null) or foreign (to be set to undefined)
                               ABS.TSimple qtyp -> return $ HS.FieldUpdate (HS.UnQual $ HS.Ident $ fid ++ "'" ++ clsName) 
                                                  (let (prefix, ident) = splitQType qtyp
                                                       Just (SV symbolType _) = if null prefix
                                                                               then M.lookup (SN ident Nothing) ?st
                                                                               else M.lookup (SN ident (Just (prefix, False))) ?st 
                                                                                        <|> M.lookup (SN ident (Just (prefix, True))) ?st 
                                                   in case symbolType of
                                                        Interface _ _ -> [hs| $(HS.Var $ HS.UnQual $ HS.Ident $ showQType qtyp) null |]
                                                        Foreign -> [hs| undefined |]
                                                        _ -> errorPos p "A field must be initialised if it is not of a reference type"
                                                  ) : acc
                               -- it may be foreign (to be set to undefined)
                               ABS.TGen qtyp _ -> return $ HS.FieldUpdate (HS.UnQual $ HS.Ident $ fid ++ "'" ++ clsName) 
                                                  (let (prefix, ident) = splitQType qtyp
                                                       Just (SV symbolType _) = if null prefix
                                                                                then M.lookup (SN ident Nothing) ?st
                                                                                else M.lookup (SN ident (Just (prefix, False))) ?st 
                                                                                        <|> M.lookup (SN ident (Just (prefix, True))) ?st 
                                                   in case symbolType of
                                                        Foreign -> [hs| undefined |]
                                                        _ -> errorPos p "A field must be initialised if it is not of a reference type"
                                                  ) : acc
                               ABS.TUnderscore -> errorPos p "Cannot infer type of field which has not been assigned"

                   ABS.MethClassBody _ _ _ _ -> case mInit of
                               ABS.NoBlock -> return acc -- ignore, TODO: maybe this allows methclassbody to be intertwined with fieldbody
                               ABS.JustBlock _ _-> fail "Second parsing error: Syntactic error, no method declaration accepted here"

                          )
                   [] ldecls)
        M.empty) Nothing]

  : -- The init'Class function
  [HS.FunBind [HS.Match noLoc (HS.Ident $ "init'" ++ clsName)
               [HS.PVar $ HS.Ident "this"] -- this, the only param
               Nothing 
               (HS.UnGuardedRhs $
                  case mInit of
                    ABS.NoBlock -> if "run" `M.member` aloneMethods
                                  then [hs| (this <!!> run) :: I'.IO () |]
                                  else [hs| (return ()) :: I'.IO () |]
                    ABS.JustBlock _ block -> if "run" `M.member` aloneMethods
                                            then [hs| ($(tMethod block [] fields clsName) >> this <!!> run) :: I'.IO () |]
                                            else [hs| ($(tMethod block [] fields clsName)) :: I'.IO () |]
               ) (Just aloneWhereClause)] ]
    

  ++  -- The direct&indirect instances for interfaces
  concatMap (\ qtyp -> let 
    (prefix, ident) = splitQType qtyp
    Just (SV (Interface directMethods extends) _) = if null prefix
                                                    then M.lookup (SN ident Nothing) ?st
                                                    else M.lookup (SN ident (Just (prefix, False))) ?st 
                                                             <|> M.lookup (SN ident (Just (prefix, True))) ?st 
                      in 
    -- the direct instances
    HS.InstDecl noLoc Nothing [] [] 
          (HS.UnQual $ HS.Ident $ showQType qtyp ++ "'") -- the interface name
          [HS.TyCon $ HS.UnQual $ HS.Ident $ clsName] -- the class name
          (fmap (\ mname -> let Just (ABS.MethClassBody typ _ mparams block) = M.lookup mname classMethods
                           in HS.InsDecl (HS.FunBind  [HS.Match noLoc (HS.Ident mname)
                                                       -- method params
                                                       (map (\ (ABS.Par _ (ABS.LIdent (_,pid))) -> HS.PVar (HS.Ident pid)) mparams ++ [HS.PVar $ HS.Ident "this"])
                                                       Nothing 
                                                       (HS.UnGuardedRhs $ tMethod block mparams fields clsName) (Just aloneWhereClause)])
                ) directMethods)
    -- the indirect instances
    : M.foldlWithKey (\ acc (SN n _) indirectMethods ->
                          HS.InstDecl noLoc Nothing [] [] 
                                (HS.UnQual $ HS.Ident $ n ++ "'") -- the interface name
                                [HS.TyCon $ HS.UnQual $ HS.Ident $ clsName] -- the class name
                                (fmap (\ mname -> let Just (ABS.MethClassBody typ _ mparams block) = M.lookup mname classMethods
                                                 in HS.InsDecl (HS.FunBind  [HS.Match noLoc (HS.Ident mname) 
                                                                             -- method params
                                                                             (map (\ (ABS.Par _ (ABS.LIdent (_,pid))) -> HS.PVar (HS.Ident pid)) mparams ++ [HS.PVar $ HS.Ident "this"])
                                                                             Nothing 
                                                                             (HS.UnGuardedRhs $ tMethod block mparams fields clsName) (Just aloneWhereClause)])
                                      ) indirectMethods) : acc
                     ) [] extends
            ) impls

  ++ -- the rest alone, non-interface methods, named as:  method''Class
  map (\ (mname, ABS.MethClassBody typ _ mparams block) ->
           (HS.FunBind  [HS.Match noLoc (HS.Ident $ mname ++ "''" ++ clsName)
                         -- method params
                         (map (\ (ABS.Par _ (ABS.LIdent (_,pid))) -> HS.PVar (HS.Ident pid)) mparams ++ [HS.PVar $ HS.Ident "this"])
                         Nothing 
                         (HS.UnGuardedRhs $ tMethod block mparams fields clsName) Nothing]) )
          (M.assocs aloneMethods)

  where
    -- The method names (both implementing & alone methods) of this class mapped to their bodies
    classMethods :: M.Map String ABS.ClassBody
    classMethods = M.fromList $ mapMaybe (\case 
                                     m@(ABS.MethClassBody _ (ABS.LIdent (_,ident)) _ _) -> Just (ident,m)
                                     _ -> Nothing)
                                    (case mInit of
                                       ABS.NoBlock -> ldecls
                                       ABS.JustBlock _ _ -> rdecls)

    -- All (class-params and declared) fields of this class
    fields :: M.Map ABS.LIdent ABS.Type -- order matters, because the fields are indexed
    fields = M.fromList $ map (\ (ABS.Par t i) -> (i,t)) cparams ++ mapMaybe (\case
                                                                               ABS.FieldClassBody t i -> Just (i,t)
                                                                               ABS.FieldAssignClassBody t i _ -> Just (i,t)
                                                                               ABS.MethClassBody _ _ _ _ -> Nothing
                                                                              ) ldecls

    aloneMethods :: M.Map String ABS.ClassBody
    aloneMethods = M.filterWithKey (\ m _ -> m `notElem` toImplementMethods) classMethods
        where
          toImplementMethods :: [String]
          toImplementMethods = concatMap (\ (SV (Interface dmethods extends) _) -> concat $ dmethods : M.elems extends) $
                         M.elems $ M.filterWithKey (\ (SN i _) _ -> i `elem` map (snd . splitQType) impls) ?st

    aloneWhereClause :: HS.Binds
    aloneWhereClause = HS.BDecls $ map (\ aloneMethodLocal ->
                                            let aloneMethodTop = HS.Var $ HS.UnQual $ HS.Ident $ aloneMethodLocal ++ "''" ++ clsName
                                            in [dec| __aloneMethodLocal__ = $aloneMethodTop |]) $ M.keys aloneMethods

-- Type synonyms
tDecl (ABS.TypeDecl (ABS.UIdent (_,tid)) typ) = [ [dec| type U_tid_U = $(tType typ) |] ]

-- Type synonyms with variables
tDecl (ABS.TypeParDecl (ABS.UIdent (_,tid)) tyvars typ) = [HS.TypeDecl noLoc (HS.Ident tid) 
                                                                 (map (\ (ABS.UIdent (_,varid)) -> 
                                                                           HS.UnkindedVar $ HS.Ident $ headToLower varid)
                                                                  tyvars)
                                                                 (tTypeOrTyVar tyvars typ)
                                                          ]

-- Datatypes
tDecl (ABS.DataParDecl (ABS.UIdent (_,tid)) tyvars constrs) =  HS.DataDecl noLoc HS.DataType [] (HS.Ident tid) 

          -- Type Variables
          (map (\ (ABS.UIdent (_,varid)) -> HS.UnkindedVar $ HS.Ident $ headToLower varid) tyvars)

          -- Data Constructors
          (map (\case
                ABS.SinglConstrIdent (ABS.UIdent (_,cid)) -> HS.QualConDecl noLoc [] [] (HS.ConDecl (HS.Ident cid) []) 
                ABS.ParamConstrIdent (ABS.UIdent (_,cid)) args -> HS.QualConDecl noLoc [] [] (HS.ConDecl (HS.Ident cid) (map (HS.TyBang HS.BangedTy . tTypeOrTyVar tyvars . typOfConstrType) args))) constrs) -- TODO: maybe only allow Banged Int,Double,... like the class-datatype

          -- Deriving
           ([(HS.Qual (HS.ModuleName "I'") $ HS.Ident "Eq", []), (HS.Qual (HS.ModuleName "I'") $ HS.Ident "Show", [])])

          -- Extra record-accessor functions
          : map (\ (ABS.LIdent (_,fname), consname, idx, len) ->  
                     HS.FunBind [HS.Match noLoc (HS.Ident fname) ([HS.PApp (HS.UnQual (HS.Ident consname)) (replicate idx HS.PWildCard ++ [HS.PVar (HS.Ident "a")] ++ replicate (len - idx - 1) HS.PWildCard)]) Nothing (HS.UnGuardedRhs (HS.Var (HS.UnQual (HS.Ident "a")))) Nothing]) (
             concatMap (\case
               ABS.SinglConstrIdent _ -> []
               ABS.ParamConstrIdent (ABS.UIdent (_,cid)) args -> -- taking the indices of fields
                                         let len = length args
                                         in
                                            foldl (\ acc (field, idx) ->  case field of
                                                                            ABS.EmptyConstrType _ -> acc
                                                                            ABS.RecordConstrType _ fid -> (fid, cid, idx, len):acc) [] (zip args [0..])
              ) constrs )
    where
      typOfConstrType :: ABS.ConstrType -> ABS.Type
      typOfConstrType (ABS.EmptyConstrType typ) = typ
      typOfConstrType (ABS.RecordConstrType typ _) = typ

         

-- Interfaces
tDecl (ABS.ExtendsDecl (ABS.UIdent (_,tname)) extends ms) = HS.ClassDecl noLoc 
        (map (\ qtyp -> HS.ClassA (HS.UnQual $ HS.Ident $ showQType qtyp ++ "'") [HS.TyVar (HS.Ident "a")]) extends) -- super-interfaces
        (HS.Ident $ tname ++ "'") -- name of interface
        [HS.UnkindedVar (HS.Ident "a")] -- all interfaces have kind * -> *
        []
        (map (tMethSig tname) ms)
      : -- Existential Wrapper
      HS.DataDecl noLoc HS.DataType [] (HS.Ident tname) [] [HS.QualConDecl noLoc [HS.UnkindedVar $ HS.Ident "a"] [HS.ClassA (HS.UnQual $ HS.Ident $ tname ++ "'") [HS.TyVar (HS.Ident "a")]] (HS.ConDecl (HS.Ident tname) [HS.TyApp (HS.TyCon $ HS.UnQual $ HS.Ident "Obj'") (HS.TyVar $ HS.Ident "a")])] []
      : -- Show instance for the wrapper
      HS.InstDecl noLoc Nothing [] [] (HS.Qual (HS.ModuleName "I'") $ HS.Ident "Show") [HS.TyCon $ HS.UnQual $ HS.Ident $ tname]
            [HS.InsDecl (HS.FunBind  [HS.Match noLoc (HS.Ident "show") [HS.PWildCard] Nothing (HS.UnGuardedRhs $ HS.Lit $ HS.String tname) Nothing])]
      : -- Eq instance for the wrapper
      HS.InstDecl noLoc Nothing [] [] (HS.Qual (HS.ModuleName "I'") $ HS.Ident  "Eq") [HS.TyCon $ HS.UnQual $ HS.Ident tname]
         [HS.InsDecl $ HS.FunBind [HS.Match noLoc (HS.Symbol "==") 
                                   [HS.PApp (HS.UnQual $ HS.Ident tname) [HS.PApp (HS.UnQual $ HS.Ident "Obj'") [HS.PVar $ HS.Ident "ref1'", HS.PWildCard]],
                                    HS.PApp (HS.UnQual $ HS.Ident tname) [HS.PApp (HS.UnQual $ HS.Ident "Obj'") [HS.PVar $ HS.Ident "ref2'", HS.PWildCard]]]
                                   Nothing (HS.UnGuardedRhs $ HS.InfixApp 
                                                  (HS.Var $ HS.UnQual $ HS.Ident "ref1'") 
                                                  (HS.QVarOp $ HS.UnQual $ HS.Symbol "==") 
                                                  (HS.App (HS.Var $ HS.Qual (HS.ModuleName "I'") $ HS.Ident "unsafeCoerce") (HS.Var $ HS.UnQual $ HS.Ident "ref2'"))) Nothing]]

       -- null class is an instance of any interface
       : HS.InstDecl noLoc Nothing [] [] (HS.UnQual $ HS.Ident $ tname ++ "'") [HS.TyCon $ HS.UnQual $ HS.Ident "Null'"] 
             (map (\ (ABS.AnnMethSig _ (ABS.MethSig _ (ABS.LIdent (_,mid)) _)) -> 
                       HS.InsDecl [dec| __mid__ = I'.error  "this should not happen. report the program to the compiler developers" |] ) ms)


      : -- Sub instance self 
      HS.InstDecl noLoc Nothing []  []
                            (HS.UnQual $ HS.Ident "Sub'")
                            (replicate 2 $ HS.TyCon $ HS.UnQual $ HS.Ident tname) -- instance Sub Interf1 Interf1
                            [   -- the upcasting method is 'id' in this case
                                HS.InsDecl $ HS.FunBind $ [HS.Match noLoc (HS.Ident "up'") [HS.PVar $ HS.Ident "x'"] Nothing 
                                                           (HS.UnGuardedRhs $ HS.Var $ HS.UnQual $ HS.Ident "x'") Nothing]
                            ]

      : -- Sub instance for unwrapped this & null
      HS.InstDecl noLoc Nothing []
            [HS.ClassA (HS.UnQual $ HS.Ident (tname ++ "'")) [HS.TyVar $ HS.Ident "a"]] -- context
            (HS.UnQual $ HS.Ident "Sub'")  -- instance (I1' a) => Sub (Obj' a) I1
            [ HS.TyApp (HS.TyCon $ HS.UnQual $ HS.Ident "Obj'") (HS.TyVar $ HS.Ident "a")
            , HS.TyCon $ HS.UnQual $ HS.Ident $ tname]
            [   -- the upcasting method
                -- is wrapping with the constructor
                HS.InsDecl $ HS.FunBind $ [HS.Match noLoc (HS.Ident "up'") [] Nothing 
                                                 (HS.UnGuardedRhs $ (HS.Con $ HS.UnQual $ HS.Ident tname)
                                                 ) Nothing] ]

      : -- Sub instances of all direct AND indirect supertypes
      generateSubForAllSupers

    where
    -- method_signature :: args -> Obj a (THIS) -> (res -> ABS ()) -> ABS ()
    tMethSig :: String -> ABS.AnnotMethSignat -> HS.ClassDecl
    tMethSig interName (ABS.AnnMethSig _ (ABS.MethSig retTyp (ABS.LIdent (mpos,mname)) params)) = 
        if mname == "run" && ((case retTyp of
                              ABS.TSimple (ABS.QTyp [ABS.QTypeSegmen (ABS.UIdent (_, "Unit"))]) -> True
                              _ -> False) || not (null params))
        then errorPos mpos "run should have zero parameters and return type Unit"
        else HS.ClsDecl $ HS.TypeSig noLoc [HS.Ident mname] $
               foldr  -- function application is right-associative
                 (\ tpar acc -> HS.TyFun tpar acc)
                 (HS.TyApp (HS.TyCon $ HS.UnQual $ HS.Ident "ABS'") (tType retTyp))
                 (map (\ (ABS.Par typ _) -> tType typ) params ++ [(HS.TyApp (HS.TyCon $ HS.UnQual $ HS.Ident "Obj'") (HS.TyVar $ HS.Ident "a"))]) -- last param is this

    generateSubForAllSupers :: (?st :: SymbolTable) => [HS.Decl]
    generateSubForAllSupers = case M.lookup (SN tname Nothing) ?st of
                     Just (SV (Interface _ all_extends) _) -> map 
                      (\ (SN sup _) -> HS.InstDecl noLoc Nothing [] []
                       (HS.UnQual $ HS.Ident "Sub'")
                       [HS.TyCon $ HS.UnQual $ HS.Ident tname, HS.TyCon $ HS.UnQual $ HS.Ident sup] -- instance Sub SubInterf SupInterf
                       [   -- the upcasting method is unwrapping and wrapping the data constructors
                          HS.InsDecl $ HS.FunBind $ [HS.Match noLoc (HS.Ident "up'") [HS.PApp (HS.UnQual $ HS.Ident tname) [HS.PVar $ HS.Ident "x'"]] Nothing 
                                                           (HS.UnGuardedRhs $ HS.App (HS.Con $ HS.UnQual $ HS.Ident sup)
                                                                  (HS.Var $ HS.UnQual $ HS.Ident "x'")) Nothing]
                       ])
                      (M.keys all_extends)
                     _ -> error "development error at firstpass"
                    
    
