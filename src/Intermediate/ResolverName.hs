module Intermediate.ResolverName where

import List
import Monad
import Data.Maybe
import Control.Monad.State

import Common
import Front.Absclafer
import Intermediate.Intclafer

data SEnv = SEnv {
  clafers :: [IClafer],
  context :: Maybe IClafer,
  bindings :: [String],
  resPath :: [IClafer]
  } deriving Show


resolveDeclaration :: IModule -> IDeclaration -> IDeclaration
resolveDeclaration declarations x = case x of
  IClaferDecl clafer  -> IClaferDecl $ resolveClafer env clafer
  IConstDecl constraint  -> IConstDecl $ resolveLExp env constraint
  where
  env = SEnv (toClafers declarations) Nothing [] []


resolveClafer :: SEnv -> IClafer -> IClafer
resolveClafer env clafer =
  clafer {elements = map (resolveElement env {context = Just clafer}) $
                     elements clafer}


resolveSuper :: SEnv -> ISuper -> ISuper
resolveSuper env x = case x of
  ISuper True sexp -> ISuper True $ map (resolveSExp env) sexp
  _ -> x


resolveElement :: SEnv -> IElement -> IElement
resolveElement env x = case x of
  ISubclafer clafer  -> ISubclafer $ resolveClafer env clafer
  ISubconstraint constraint  -> ISubconstraint $ resolveLExp env constraint


resolveLExp :: SEnv -> ILExp -> ILExp
resolveLExp env x = case x of
  IEIff lexp0 lexp -> IEIff (res lexp0) (res lexp)
  IEImpliesElse lexp0 lexp Nothing -> IEImpliesElse (res lexp0) (res lexp) Nothing
  IEImpliesElse lexp0 lexp1 (Just lexp) -> IEImpliesElse (res lexp0) (res lexp1) (Just $ res lexp)
  IEOr lexp0 lexp -> IEOr (res lexp0) (res lexp)
  IEXor lexp0 lexp -> IEXor (res lexp0) (res lexp)
  IEAnd lexp0 lexp -> IEAnd (res lexp0) (res lexp)
  IENeg lexp -> IENeg (res lexp)
  IETerm term -> IETerm (resolveTerm env term)
  where
  res = resolveLExp env


resolveTerm :: SEnv -> ITerm -> ITerm
resolveTerm env x = case x of
  ITermCmpExp cmpexp -> ITermCmpExp $ resolveCmpExp env cmpexp
  ITermQuantSet quant sexp -> ITermQuantSet quant $ resolveSExp env sexp
  ITermQuantDeclExp decls lexp -> ITermQuantDeclExp
    decls' (resolveLExp env' lexp)
    where
    (decls', env') = runState (mapM processDecl decls) env


processDecl decl = do
  env <- get
  modify (\e -> e { bindings = getIdents decl ++ bindings e })
  return $ resolveDecl env decl


getIdents (Decl _ _ locids _) = map
  (\(LocIdIdent ident) -> transIdent ident) locids


resolveDecl :: SEnv -> Decl -> Decl
resolveDecl env x = case x of
  Decl exquant disj locids sexp -> Decl exquant disj locids $
                                   resolveSExp env sexp

resolveCmpExp :: SEnv -> CmpExp -> CmpExp
resolveCmpExp env x = case x of
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
  res = resolveExp env


resolveExp :: SEnv -> Exp -> Exp
resolveExp env x = case x of
  ESetExp  sexp -> ESetExp $ resolveSExp env sexp
  ENumExp aexp -> ENumExp $ resolveAExp env aexp
  EStrExp strexp -> x


resolveSExp :: SEnv -> SExp -> SExp
resolveSExp env x = case x of
  SExpUnion sexp0 sexp -> SExpUnion (res sexp0) (res sexp)
  SExpIntersection sexp0 sexp  -> SExpIntersection (res sexp0) (res sexp)
  SExpDomain sexp0 sexp  -> SExpDomain (res sexp0) (res sexp)
  SExpRange sexp0 sexp  -> SExpRange (res sexp0) (res sexp)
  SExpJoin sexp0 sexp  -> snd $ resolveNav env x True
  SExpIdent id -> snd $ resolveNav env x True
  where
  res = resolveSExp env


resolveNav :: SEnv -> SExp -> Bool -> (Maybe IClafer, SExp)
resolveNav env x isFirst = case x of
  SExpJoin sexp0 sexp  -> (context'', SExpJoin sexp0' sexp')
    where
    (context', sexp0') = resolveNav env sexp0 True
    (context'', sexp') = resolveNav env {context = context'} sexp False
  SExpIdent id -> (fst $ findName env $ getStart out, out)              
    where
    out
      | isFirst   = mkPath env $ fst $ resolveName env $ transIdent id
      | otherwise = SExpIdent $ Ident $ fst $ resolveImmName env $ transIdent id


mkPath :: SEnv -> String -> SExp
mkPath env id
  | isNothing clafer || null spath || null path' = SExpIdent $ Ident id
  | otherwise = toNav $ reverse $ map uid spath
  where
  clafer = context env
  (spath, path') = break (isEqClaferId $ uid $ fromJust clafer) $
                   snd $ findName env id
  toNav = foldl (\sexp id -> SExpJoin sexp $ SExpIdent $ Ident id)
          (SExpIdent $ Ident this)


getStart :: SExp -> String
getStart (SExpJoin sexp _) = getStart sexp
getStart (SExpIdent id)    = transIdent id


findName :: SEnv -> String -> (Maybe IClafer, [IClafer])
findName env id 
  | id == parent && context env /= Nothing && length ppath > 1 =
      (Just $ head $ tail ppath, ppath)
  | id `elem` [this, children, strType, intType, integerType] =
      (context env, ppath)
--  | (not.null) spath                             = (Just $ head spath, spath)
  | (not.null) path                              = (Just $ head path, path)
  | otherwise                                    = resolveNone env id
  where
  spath = findClafer id [] env
  path  = resolvePath id [] env $ clafers env
  ppath = resolvePath (uid $ fromJust $ context env) [] env $ clafers env

-- -----------------------------------------------------------------------------
-- analyzes arithmetic expression
resolveAExp :: SEnv -> AExp -> AExp
resolveAExp env x = case x of
  EAdd aexp0 aexp -> EAdd (res aexp0) (res aexp)
  ESub aexp0 aexp -> ESub (res aexp0) (res aexp)
  EMul aexp0 aexp -> EMul (res aexp0) (res aexp)
  EUmn aexp       -> EUmn (res aexp)
  ECSetExp sexp   -> ECSetExp $ resolveSExp env sexp
  EInt n -> x
  where
  res = resolveAExp env

-- -----------------------------------------------------------------------------

resolveName :: SEnv -> String -> (String, [IClafer])
resolveName env id = resolve env id
  [resolveSpecial, resolveBind, resolveSubclafers, resolveTopLevel, resolveNone]


resolveImmName :: SEnv -> String -> (String, [IClafer])
resolveImmName env id = resolve env id
  [resolveImmSubclafers, resolveNone]


resolve env id fs = fromJust $ foldr1 mplus $ map (\x -> x env id) fs


-- reports error if clafer not found
resolveNone env id = error $ id ++ " not found within " ++
  (show $ context env >>= (Just . ident))

-- TODO: return this or parent
-- checks if ident is one of special identifiers
resolveSpecial :: SEnv -> String -> Maybe (String, [IClafer])
resolveSpecial _ id
  | id `elem` [this, strType, intType, integerType, parent, children] =
      Just (id, [])
  | otherwise                                                         = Nothing 


-- checks if ident is bound locally
resolveBind :: SEnv -> String -> Maybe (String, [IClafer])
resolveBind env id = find (== id) (bindings env) >>= (\x -> Just (x, []))


-- searches for a name in all subclafers (BFS)
resolveSubclafers :: SEnv -> String -> Maybe (String, [IClafer])
resolveSubclafers env id =
  (context env) >> (findUnique id $ tail $ bfs toNodeDeep
                    [env {resPath = [fromJust $ context env]}])


-- searches for a name in immediate subclafers (BFS)
resolveImmSubclafers :: SEnv -> String -> Maybe (String, [IClafer])
resolveImmSubclafers env id =
  (context env) >> (findUnique id $ map (\x -> (x, [fromJust $ context env])) $
                    allSubclafers env)


-- searches for a feature starting from local root (BFS) and then continues with
-- other declarations
resolveTopLevel :: SEnv -> String -> Maybe (String, [IClafer])
resolveTopLevel env id = case context env of
  Nothing -> resolveUnique $ clafers env
  _  -> foldr1 mplus $ map resolveUnique $ pairToList $ partition
        (isEqClaferId (last $ findPath (uid $ fromJust $ context env) env)) $
        clafers env
  where
  resolveUnique xs = findUnique id $ bfs toNodeDeep $
                     map (\c -> env {context = Just c}) xs


toNodeDeep env = ((fromJust $ context env, resPath env),
                  map (\c -> env {context = Just c, resPath = c : resPath env})
                  $ allSubclafers env)


allSubclafers env = getSubclafers $ concat $
                    mapHierarchy elements (clafers env) (fromJust $ context env)


findPath :: String -> SEnv -> [String]
findPath id env = map uid $ resolvePath id [] env $ clafers env


resolvePath :: String -> [IClafer] -> SEnv -> [IClafer] -> [IClafer]
resolvePath id path env clafers = if null path' then [] else head path'
  where
  path' = filterNull $ map (findClafer id path) $ map (\c -> env {context = Just c}) clafers


findClafer :: String -> [IClafer] -> SEnv -> [IClafer]
findClafer id path env
  | id == uid clafer = clafer : path
  | otherwise        = path'
  where
  clafer = fromJust $ context env
--  path' = resolvePath id (clafer : path) $ getSubclafers $ elements clafer
  path' = resolvePath id (clafer : path) env $ allSubclafers env


findUnique :: String -> [(IClafer, [IClafer])] -> Maybe (String, [IClafer])
findUnique x xs =
  case filter (((==) x).ident.fst) xs of
    []     -> Nothing
    [elem] -> Just $ (uid $ fst elem, snd elem)
    _      -> error $ "element is not unique : " ++ show x
