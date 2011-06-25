module Intermediate.Resolver where

import List
import Monad
import Data.Maybe
import Control.Monad.State

import Common
import Front.Absclafer
import Intermediate.Intclafer



resolveModule :: IModule -> IModule
resolveModule declarations = resolveNamesModule $ nameModule declarations


-- -----------------------------------------------------------------------------
data NEnv = NEnv {num :: Int}

nameModule :: IModule -> IModule
nameModule declarations = evalState (mapM nameDeclaration declarations) (NEnv 0)


nameDeclaration x = case x of
  IClaferDecl clafer  -> IClaferDecl `liftM` (nameClafer clafer)
  IConstDecl constraint  -> return x


nameClafer clafer = do
  modify (\e -> e {num = 1 + num e})
  n <- gets num
  elements' <- mapM nameElement $ elements clafer
  return $ clafer
    {uid = concat ["cl", show n, "_",  ident clafer], elements = elements'}


nameElement x = case x of
  ISubclafer clafer -> ISubclafer `liftM` (nameClafer clafer)
  ISubconstraint ilexp -> return x

-- -----------------------------------------------------------------------------
resolveNamesModule :: IModule -> IModule
resolveNamesModule declarations =declarations'''
  where

{- multiProcess
                     (map (\f ->
                               \ps us -> f (ps ++ us) (head us))
                     [resolveNamesDeclaration, resolveSuperDeclaration])
                     declarations
-}

  declarations''' = map (resolveNamesDeclaration declarations'') declarations''
  declarations'' = map (resolveOSuperDeclaration declarations') declarations'
  declarations' = map (resolveSuperDeclaration declarations) declarations

-- -----------------------------------------------------------------------------
resolveSuperDeclaration :: IModule -> IDeclaration -> IDeclaration
resolveSuperDeclaration declarations x = case x of
  IClaferDecl clafer  -> IClaferDecl $ resolveSuperClafer declarations clafer
  IConstDecl constraint  -> x


resolveSuperClafer :: IModule -> IClafer -> IClafer
resolveSuperClafer declarations clafer =
  clafer {super = resolveSuperSuper declarations $ super clafer,
          elements = map (resolveSuperElement declarations) $ elements clafer}


resolveSuperSuper :: IModule -> ISuper -> ISuper
resolveSuperSuper declarations x = case x of
  ISuper False [SExpIdent (Ident "clafer")] -> x
  ISuper False [SExpIdent id] -> ISuper False [SExpIdent $ Ident id']
    where
    id' = fromMaybe (error "No superclafer found") $
          resolveSuper declarations $ transIdent id
  _ -> x


resolveSuperElement :: IModule -> IElement -> IElement
resolveSuperElement declarations x = case x of
  ISubclafer clafer  -> ISubclafer $ resolveSuperClafer declarations clafer
  ISubconstraint constraint  -> x

-- -----------------------------------------------------------------------------

resolveSuper :: IModule -> String -> Maybe String
resolveSuper declarations id =
  findUnique id $ filter isAbstract $ bfsClafers $ toClafers declarations


findUnique :: String -> [IClafer] -> Maybe String
findUnique x xs =
  case filter (((==) x).ident) xs of
    []     -> Nothing
    [elem] -> Just $ uid elem
    _      -> error $ "element is not unique : " ++ show x

-- -----------------------------------------------------------------------------
resolveOSuperDeclaration :: IModule -> IDeclaration -> IDeclaration
resolveOSuperDeclaration declarations x = case x of
  IClaferDecl clafer  -> IClaferDecl $ resolveOSuperClafer env clafer
  IConstDecl constraint  -> x
  where
  env = SEnv (toClafers declarations) Nothing []


resolveOSuperClafer :: SEnv -> IClafer -> IClafer
resolveOSuperClafer env clafer =
  clafer {super = resolveOSuperSuper env {context = Just clafer} $ super clafer,
          elements = map (resolveOSuperElement env {context = Just clafer}) $
          elements clafer}


resolveOSuperSuper :: SEnv -> ISuper -> ISuper
resolveOSuperSuper env x = case x of
  ISuper True sexps -> ISuper True $ map (resolveNamesSExp env) sexps
  _ -> x


resolveOSuperElement :: SEnv -> IElement -> IElement
resolveOSuperElement env x = case x of
  ISubclafer clafer  -> ISubclafer $ resolveOSuperClafer env clafer
  ISubconstraint constraint  -> x

-- -----------------------------------------------------------------------------
data SEnv = SEnv {
  clafers :: [IClafer],
  context :: Maybe IClafer,
  bindings :: [String]
  } deriving Show


resolveNamesDeclaration :: IModule -> IDeclaration -> IDeclaration
resolveNamesDeclaration declarations x = case x of
  IClaferDecl clafer  -> IClaferDecl $ resolveNamesClafer env clafer
  IConstDecl constraint  -> IConstDecl $ resolveNamesLExp env constraint
  where
  env = SEnv (toClafers declarations) Nothing []


resolveNamesClafer :: SEnv -> IClafer -> IClafer
resolveNamesClafer env clafer =
  clafer {elements = map (resolveNamesElement env {context = Just clafer}) $
                     elements clafer}


resolveNamesSuper :: SEnv -> ISuper -> ISuper
resolveNamesSuper env x = case x of
  ISuper True sexp -> ISuper True $ map (resolveNamesSExp env) sexp
  _ -> x


resolveNamesElement :: SEnv -> IElement -> IElement
resolveNamesElement env x = case x of
  ISubclafer clafer  -> ISubclafer $ resolveNamesClafer env clafer
  ISubconstraint constraint  -> ISubconstraint $ resolveNamesLExp env constraint


resolveNamesLExp :: SEnv -> ILExp -> ILExp
resolveNamesLExp env x = case x of
  IEIff lexp0 lexp -> IEIff (res lexp0) (res lexp)
  IEImpliesElse lexp0 lexp Nothing -> IEImpliesElse (res lexp0) (res lexp) Nothing
  IEImpliesElse lexp0 lexp1 (Just lexp) -> IEImpliesElse (res lexp0) (res lexp1) (Just $ res lexp)
  IEOr lexp0 lexp -> IEOr (res lexp0) (res lexp)
  IEXor lexp0 lexp -> IEXor (res lexp0) (res lexp)
  IEAnd lexp0 lexp -> IEAnd (res lexp0) (res lexp)
  IENeg lexp -> IENeg (res lexp)
  IETerm term -> IETerm (resolveNamesTerm env term)
  where
  res = resolveNamesLExp env


resolveNamesTerm :: SEnv -> ITerm -> ITerm
resolveNamesTerm env x = case x of
  ITermCmpExp cmpexp -> ITermCmpExp $ resolveNamesCmpExp env cmpexp
  ITermQuantSet quant sexp -> ITermQuantSet quant $ resolveNamesSExp env sexp
  ITermQuantDeclExp decls lexp -> ITermQuantDeclExp
    decls' (resolveNamesLExp env' lexp)
    where
    (decls', env') = runState (mapM processDecl decls) env


processDecl decl = do
  env <- get
  modify (\e -> e { bindings = getIdents decl ++ bindings e })
  return $ resolveNamesDecl env decl


getIdents (Decl _ _ locids _) = map
  (\(LocIdIdent ident) -> transIdent ident) locids


resolveNamesDecl :: SEnv -> Decl -> Decl
resolveNamesDecl env x = case x of
  Decl exquant disj locids sexp -> Decl exquant disj locids $
                                   resolveNamesSExp env sexp

resolveNamesCmpExp :: SEnv -> CmpExp -> CmpExp
resolveNamesCmpExp env x = case x of
  ELt exp0 exp  -> ELt (res exp0) (res exp)
  EGt exp0 exp  -> EGt (res exp0) (res exp)
  EREq exp0 exp -> EREq (res exp0) (res exp)
  EEq exp0 exp  -> EEq (res exp0) (res exp)
  ELte exp0 exp  -> ELte (res exp0) (res exp)
  EGte exp0 exp  -> EGte (res exp0) (res exp)
  ENeq exp0 exp  -> ENeq (res exp0) (res exp)
  ERNeq exp0 exp -> ERNeq (res exp0) (res exp)
  EIn exp0 exp   -> EIn (res exp0) (res exp)
  ENin exp0 exp  -> ENin (res exp0) (res exp)
  where
  res = resolveNamesExp env


resolveNamesExp :: SEnv -> Exp -> Exp
resolveNamesExp env x = case x of
  ESetExp  sexp -> ESetExp $ resolveNamesSExp env sexp
  ENumExp aexp -> ENumExp $ resolveNamesAExp env aexp
  EStrExp strexp -> x


resolveNamesSExp :: SEnv -> SExp -> SExp
resolveNamesSExp env x = case x of
  SExpUnion sexp0 sexp -> SExpUnion (res sexp0) (res sexp)
  SExpIntersection sexp0 sexp  -> SExpIntersection (res sexp0) (res sexp)
  SExpDomain sexp0 sexp  -> SExpDomain (res sexp0) (res sexp)
  SExpRange sexp0 sexp  -> SExpRange (res sexp0) (res sexp)
  SExpJoin sexp0 sexp  -> snd $ resolveNamesNav env x True
  SExpIdent id -> snd $ resolveNamesNav env x True
  where
  res = resolveNamesSExp env


resolveNamesNav :: SEnv -> SExp -> Bool -> (Maybe IClafer, SExp)
resolveNamesNav env x isFirst = case x of
  SExpJoin sexp0 sexp  -> (context'', SExpJoin sexp0' sexp')
    where
    (context', sexp0') = resolveNamesNav env sexp0 True
    (context'', sexp') = resolveNamesNav env {context = context'} sexp False
  SExpIdent id -> (findName env id', SExpIdent $ Ident $ id')
    where
    id' = (if isFirst then resolveName else resolveImmName) env $ transIdent id

s = SEnv {clafers = [IClafer {isAbstract = True, gcard = Nothing, ident = "comp", uid = "cl1_comp", super = ISuper {isOverlapping = False, supers = [SExpIdent (Ident "clafer")]}, card = Nothing, elements = [ISubclafer (IClafer {isAbstract = False, gcard = Nothing, ident = "version", uid = "cl2_version", super = ISuper {isOverlapping = True, supers = [SExpIdent (Ident "integer")]}, card = Nothing, elements = []})]},IClafer {isAbstract = True, gcard = Nothing, ident = "ECU", uid = "cl3_ECU", super = ISuper {isOverlapping = False, supers = [SExpIdent (Ident "cl1_comp")]}, card = Nothing, elements = []},IClafer {isAbstract = True, gcard = Nothing, ident = "display", uid = "cl4_display", super = ISuper {isOverlapping = False, supers = [SExpIdent (Ident "cl1_comp")]}, card = Nothing, elements = [ISubclafer (IClafer {isAbstract = False, gcard = Nothing, ident = "server", uid = "cl5_server", super = ISuper {isOverlapping = True, supers = [SExpIdent (Ident "ECU")]}, card = Nothing, elements = []}),ISubconstraint (IETerm (ITermCmpExp (EGte (ESetExp (SExpIdent (Ident "version"))) (ESetExp (SExpJoin (SExpIdent (Ident "server")) (SExpIdent (Ident "version")))))))]}], context = Just (IClafer {isAbstract = True, gcard = Nothing, ident = "display", uid = "cl4_display", super = ISuper {isOverlapping = False, supers = [SExpIdent (Ident "cl1_comp")]}, card = Nothing, elements = [ISubclafer (IClafer {isAbstract = False, gcard = Nothing, ident = "server", uid = "cl5_server", super = ISuper {isOverlapping = True, supers = [SExpIdent (Ident "ECU")]}, card = Nothing, elements = []}),ISubconstraint (IETerm (ITermCmpExp (EGte (ESetExp (SExpIdent (Ident "version"))) (ESetExp (SExpJoin (SExpIdent (Ident "server")) (SExpIdent (Ident "version")))))))]}), bindings = []}

z = SExpIdent (Ident "server")

(o, e) = resolveNamesNav s  z True

s' = s {context = o}

x = resolveNamesNav s' (SExpIdent (Ident "version")) False


-- -----------------------------------------------------------------------------
-- analyzes arithmetic expression
resolveNamesAExp :: SEnv -> AExp -> AExp
resolveNamesAExp env x = case x of
  EAdd aexp0 aexp -> EAdd (res aexp0) (res aexp)
  ESub aexp0 aexp -> ESub (res aexp0) (res aexp)
  EMul aexp0 aexp -> EMul (res aexp0) (res aexp)
  EUmn aexp       -> EUmn (res aexp)
  ECSetExp sexp   -> ECSetExp $ resolveNamesSExp env sexp
  EInt n -> x
  where
  res = resolveNamesAExp env

-- -----------------------------------------------------------------------------

resolveName :: SEnv -> String -> String
resolveName env id = resolve env id
  [resolveSpecial, resolveBind, resolveSubclafers, resolveTopLevel, resolveNone]


resolveImmName :: SEnv -> String -> String
resolveImmName env id = resolve env id
  [resolveImmSubclafers, resolveNone]


resolve env id fs = fromJust $ foldr1 mplus $ map (\x -> x env id) fs


-- reports error if clafer not found
resolveNone env id = error $ id ++ " not found within " ++
  (show $ context env >>= (Just . ident))


-- checks if ident is one of special identifiers
resolveSpecial :: SEnv -> String -> Maybe String
resolveSpecial _ id
  | id `elem` [this, strType, intType, integerType, parent, children] = Just id
  | otherwise                                                         = Nothing 


-- checks if ident is bound locally
resolveBind :: SEnv -> String -> Maybe String
resolveBind env id = find (== id) (bindings env)


-- searches for a name in all subclafers (BFS)
resolveSubclafers :: SEnv -> String -> Maybe String
resolveSubclafers env id =
  (context env) >> (findUnique id $ tail $ bfs toNodeDeep [env])


-- searches for a name in immediate subclafers (BFS)
resolveImmSubclafers :: SEnv -> String -> Maybe String
resolveImmSubclafers env id =
  (context env) >> (findUnique id $ allSubclafers env)


-- searches for a feature starting from local root (BFS) and then continues with
-- other declarations
resolveTopLevel :: SEnv -> String -> Maybe String
resolveTopLevel env id = case context env of
  Nothing -> resolvePath $ clafers env
  _  -> foldr1 mplus $ map resolvePath $ pairToList $ partition
        (isEqClaferId (last $ findPath (uid $ fromJust $ context env) $
                       clafers env)) $ clafers env
  where
  resolvePath xs = findUnique id $ bfs toNodeDeep $
                   map (\c -> env {context = Just c}) xs


toNodeDeep env = (fromJust $ context env,
                  map (\c -> env {context = Just c}) $ allSubclafers env)


allSubclafers env = getSubclafers $ concat $
                    mapHierarchy elements (clafers env) (fromJust $ context env)


findPath :: String -> [IClafer] -> [String]
findPath id clafers = map uid $ resolveClafer id [] clafers


resolveClafer :: String -> [IClafer] -> [IClafer] -> [IClafer]
resolveClafer id path clafers = if (not.null) path' then head path' else []
  where
  path' = filter (not.null) $ map (findClafer id path) clafers


findClafer :: String -> [IClafer] -> IClafer -> [IClafer]
findClafer id path clafer
  | id == uid clafer = clafer : path
  | otherwise        = path
  where
  path = resolveClafer id (clafer : path) $ getSubclafers $ elements clafer


findName :: SEnv -> String -> Maybe IClafer
findName env id 
  | id == parent && context env /= Nothing && length ppath > 1 =
      Just $ head $ tail ppath
  | id `elem` [this, children, strType, intType, integerType] = context env
  | (not.null) path                              = Just $ head path
  | otherwise                                    = resolveNone env id
  where
  path  = resolveClafer id [] $ clafers env
  ppath = resolveClafer (uid $ fromJust $ context env) [] $ clafers env