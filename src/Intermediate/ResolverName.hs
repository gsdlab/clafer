module Intermediate.ResolverName where

import List
import Monad
import Data.Maybe
import Control.Monad.State
import Data.Function

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
  clafer {elements = map (resolveElement env
  {context = Just clafer, resPath = clafer : resPath env}) $ elements clafer}


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
  modify (\e -> e { bindings = decls decl ++ bindings e })
  return $ decl {body = resolveSExp env $ body decl}


resolveCmpExp :: SEnv -> ICmpExp -> ICmpExp
resolveCmpExp env x = case x of
  IELt exp0 exp  -> on IELt res exp0 exp
  IEGt exp0 exp  -> on IEGt res exp0 exp
  IEREq exp0 exp -> on IEREq res exp0 exp
  IEEq exp0 exp  -> on IEEq res exp0 exp
  IELte exp0 exp  -> on IELte res exp0 exp
  IEGte exp0 exp  -> on IEGte res exp0 exp
  IENeq exp0 exp  -> on IENeq res exp0 exp
  IERNeq exp0 exp -> on IERNeq res exp0 exp
  IEIn exp0 exp   -> on IEIn res exp0 exp
  IENin exp0 exp  -> on IENin res exp0 exp
  where
  res =  resolveExp env


resolveExp :: SEnv -> IExp -> IExp
resolveExp env x = case x of
  IESetExp  sexp -> IESetExp $ resolveSExp env sexp
  IENumExp aexp -> IENumExp $ resolveAExp env aexp
  IEStrExp strexp -> x


resolveSExp :: SEnv -> ISExp -> ISExp
resolveSExp env x = case x of
  ISExpUnion sexp0 sexp -> on ISExpUnion res sexp0 sexp
  ISExpIntersection sexp0 sexp  -> on ISExpIntersection res sexp0 sexp
  ISExpDomain sexp0 sexp  -> on ISExpDomain res sexp0 sexp
  ISExpRange sexp0 sexp  -> on ISExpRange res sexp0 sexp
  ISExpJoin _ _  -> snd $ resolveNav env x True
  ISExpIdent _ _ -> snd $ resolveNav env x True
  where
  res = resolveSExp env


resolveNav :: SEnv -> ISExp -> Bool -> (Maybe IClafer, ISExp)
resolveNav env x isFirst = case x of
  ISExpJoin sexp0 sexp  -> (context'', ISExpJoin sexp0' sexp')
    where
    (context', sexp0') = resolveNav env sexp0 True
    (context'', sexp') = resolveNav env {context = context'} sexp False
  ISExpIdent id _ -> out        
    where
    out
      | isFirst   = mkPath env $ resolveName env id
      | otherwise = (Just $ head $ snd ctx, ISExpIdent (fst ctx) False)
    ctx = resolveImmName env id


mkPath :: SEnv -> (String, [IClafer]) -> (Maybe IClafer, ISExp)
mkPath env (id, path)
  | null path = (context env, id')
  | id `elem` [this, parent, children] = (Just $ head path, ISExpIdent id True)
  | id `elem` [strType, intType, integerType] = (Nothing, ISExpIdent id True)
  | isSubclafer (context env) path =
      (Just $ head path, toNav $ tail $ reverse $ map uid path)
  | otherwise = (Just $ head path, toNav' $ reverse $ map uid path)
  where
  id'   = ISExpIdent id False
  toNav = foldl (\sexp id -> ISExpJoin sexp $ ISExpIdent id False)
          (ISExpIdent this True)
  toNav' p = mkNav $ map (\c -> ISExpIdent c $ isTopLevel c $ clafers env) p


isSubclafer clafer path = (isJust clafer) &&
                          ((uid $ last path) == (uid $ fromJust clafer))


isTopLevel id clafers = id `elem` (map uid clafers)


mkNav (x:[]) = x
mkNav xs = foldl1 ISExpJoin xs

getStart :: ISExp -> String
getStart (ISExpJoin sexp _) = getStart sexp
getStart (ISExpIdent id _)  = id


-- -----------------------------------------------------------------------------
-- analyzes arithmetic expression
resolveAExp :: SEnv -> IAExp -> IAExp
resolveAExp env x = case x of
  IEAdd aexp0 aexp -> on IEAdd res aexp0 aexp
  IESub aexp0 aexp -> on IESub res aexp0 aexp
  IEMul aexp0 aexp -> on IEMul res aexp0 aexp
  IEUmn aexp       -> IEUmn $ res aexp
  IECSetExp sexp   -> IECSetExp $ resolveSExp env sexp
  IEInt n -> x
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
  (show $ context env >>= (Just . ident)) ++ show env


-- checks if ident is one of special identifiers
resolveSpecial :: SEnv -> String -> Maybe (String, [IClafer])
resolveSpecial env id
  | id `elem` [this, children] =
      Just (id, (fromJust $ context env) : resPath env)
  | id == parent = Just (id, resPath env)
  | id `elem` [strType, intType, integerType] = Just (id, [])
  | otherwise                                 = Nothing 


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
  (context env) >> (findUnique id $ map (\x -> (x, [x,fromJust $ context env]))
                    $ allSubclafers env)


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
                     map (\c -> env {context = Just c, resPath = [c]}) xs


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
