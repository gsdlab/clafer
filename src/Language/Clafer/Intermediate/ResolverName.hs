{-# LANGUAGE FlexibleContexts #-}

{-
 Copyright (C) 2012 Kacper Bak, Jimmy Liang <http://gsd.uwaterloo.ca>

 Permission is hereby granted, free of charge, to any person obtaining a copy of
 this software and associated documentation files (the "Software"), to deal in
 the Software without restriction, including without limitation the rights to
 use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 of the Software, and to permit persons to whom the Software is furnished to do
 so, subject to the following conditions:

 The above copyright notice and this permission notice shall be included in all
 copies or substantial portions of the Software.

 THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 SOFTWARE.
-}
module Language.Clafer.Intermediate.ResolverName where

import Control.Applicative
import Control.Monad
import Control.Monad.Error
import Control.Monad.Maybe
import Control.Monad.State
import Data.Maybe
import Data.Function
import Data.List

import Language.ClaferT
import Language.Clafer.Common
import Language.Clafer.Intermediate.Intclafer
import qualified Language.Clafer.Intermediate.Intclafer as I

-- | this environment is created for each clafer 
data SEnv = SEnv {
  clafers :: [IClafer],                 -- (constant) top level clafers
  context :: Maybe IClafer,             -- context of a constraint
  subClafers :: [(IClafer, [IClafer])], -- descendans (BFS)
  ancClafers :: [(IClafer, [IClafer])], -- ancesors (BFS)
  bindings :: [([(UID, MUID)], [IClafer])],  -- local names
  resPath :: [IClafer],                 -- path to the current clafer
  genv :: GEnv,                         -- (constant)
  aClafers :: [(IClafer, [IClafer])],   -- (constant) abstract clafers (BFS)
  cClafers :: [(IClafer, [IClafer])]    -- (constant) all concrete clafers (BFS)
  } deriving Show

-- | How a given name was resolved
data HowResolved 
  = Special       -- ^ "this", "parent", "children"
  | TypeSpecial   -- ^ primitive type: integer, string, real
  | Binding       -- ^ local variable (in constraints)
  | Subclafers    -- ^ clafer's descendant
  | Reference     -- ^ resolved by a reference
  | Ancestor      -- ^ clafer's ancestor
  | AbsClafer     -- ^ abstract clafer
  | TopClafer     -- ^ non-abstract top-level clafer
  deriving (Eq, Show)
  
type Resolve = Either ClaferSErr

-- initialize the cache (env)
defSEnv :: GEnv -> [IElement]  -> SEnv
defSEnv    genv'   declarations = env {aClafers = rCl aClafers',
                                       cClafers = rCl cClafers'}
  where
  env = SEnv (toClafers declarations) Nothing [] [] [] [] genv' [] []
  rCl cs = bfs toNodeDeep $ map (\c -> env{context = Just c, resPath = [c]}) cs
  (aClafers', cClafers') = partition _isAbstract $ clafers env

checkDuplicateSiblings :: IModule -> Resolve [IElement]
checkDuplicateSiblings tree = let duplicate = checkDuplicateSiblings' $ _mDecls tree
                              in if (isJust duplicate) then let Just(name,pos') = duplicate in throwError $ SemanticErr pos' $ ("Duplicate name: " ++ name) --error
                                 else return $ _mDecls tree
                                      
checkDuplicateSiblings' :: [IElement] -> Maybe (String,Span)
checkDuplicateSiblings' tree =if (isJust check) then check
                              else checkForJust $ map checkDuplicateSiblings' elementsList
  where
    check = checkListDuplicates $ map (\c -> (_ident c, _cinPos c)) $ map (\(IEClafer eclafer) -> eclafer) $ filter isIEClafer tree
    elementsList = map (\c -> _elements c) $ map (\(IEClafer eclafer) -> eclafer) $ filter isIEClafer tree


checkForJust :: [Maybe (String,Span)] -> Maybe (String,Span)
checkForJust [] = Nothing
checkForJust (h:rest) = if (isJust h) then
                          h
                        else
                          checkForJust rest
                          
checkListDuplicates :: [(String, Span)] -> Maybe (String,Span)
checkListDuplicates list = checkListDuplicates' $ sortBy (compare `on` fst) list

checkListDuplicates' :: [(String,Span)] -> Maybe (String,Span)
checkListDuplicates' [] = Nothing
checkListDuplicates' (_:[]) = Nothing
checkListDuplicates' ((a,b):(c,d):rest) = if a == c then
                                    Just (a,b)
                                  else
                                    checkListDuplicates' ((c,d):rest)
                                    
isIEClafer :: IElement -> Bool
isIEClafer (IEClafer _) = True
isIEClafer _            = False

resolveModuleNames :: (IModule, GEnv) -> Resolve IModule
resolveModuleNames (imodule, genv') =
  do
    decls' <- checkDuplicateSiblings imodule
    mDecls' <- mapM (resolveElement (defSEnv genv' decls')) decls'
    return $ imodule{_mDecls = mDecls'}

resolveClafer :: SEnv -> IClafer -> Resolve IClafer
resolveClafer env clafer =
  do
    elements' <- mapM (resolveElement env'{subClafers = subClafers',
                                              ancClafers = ancClafers'}) $
                          _elements clafer
    return $ clafer {_elements = elements'}
  where
  env' = env {context = Just clafer, resPath = clafer : resPath env}
  subClafers' = tail $ bfs toNodeDeep [env'{resPath = [clafer]}]
  ancClafers' = (init $ tails $ resPath env) >>= (mkAncestorList env)

mkAncestorList :: SEnv -> [IClafer] -> [(IClafer, [IClafer])]
mkAncestorList env rp =
  bfs toNodeDeep [env{context = Just $ head rp, resPath = rp}]

resolveElement :: SEnv -> IElement -> Resolve IElement
resolveElement env x = case x of
  IEClafer clafer  -> IEClafer <$> resolveClafer env clafer
  IEConstraint (IConstraint muid isHard' pexp)  -> IEConstraint <$> (IConstraint muid isHard' <$> resolvePExp env pexp)
  IEGoal (IGoal muid isMaximize' pexp)  -> IEGoal <$> (IGoal muid isMaximize' <$> resolvePExp env pexp  )


resolvePExp :: SEnv -> PExp -> Resolve PExp
resolvePExp env pexp =
  do
    exp' <- resolveIExp (_inPos pexp) env $ _exp pexp
    return $ pexp {_exp = exp'}

resolveIExp :: Span -> SEnv -> IExp -> Resolve IExp
resolveIExp pos' env x = case x of
  IDeclPExp quant' decls' body' -> do
    -- process each local declaration and add it to bindings
    let (decls'', env') = runState (runErrorT $ (mapM (ErrorT . processDecl) decls')) env
    IDeclPExp quant' <$> decls'' <*> resolvePExp env' body'

  IFunExp op' exps' -> if op' == iJoin then resNav else IFunExp op' <$> mapM res exps'
  IInt _ -> return x
  IDouble _ -> return x
  IStr _ -> return x
  IClaferId _ _ _ _ -> resNav
  where
  res = resolvePExp env
  resNav = fst <$> resolveNav pos' env x True

liftError :: Monad m => Either e a -> ErrorT e m a
liftError = ErrorT . return

processDecl :: MonadState SEnv m => IDecl -> m (Resolve IDecl)
processDecl decl = runErrorT $ do
  env <- lift get
  let originalBody = _body decl
  (body', path) <- liftError $ resolveNav (_inPos $ _body decl) env (_exp originalBody) True
  lift $ modify (\e -> e { bindings = (_decls decl, path) : bindings e })
  return $ decl {_body = pExpDefPid (_pexpMUID originalBody) (_inPos originalBody) body'}

resolveNav :: Span -> SEnv -> IExp -> Bool -> Resolve (IExp, [IClafer])
resolveNav pos' env x isFirst = case x of
  IFunExp "." (pexp0:pexp1:[]) -> do
    (exp0', path0') <- resolveNav (_inPos pexp0) env                                                 (_exp pexp0) True
    (exp1', path1') <- resolveNav (_inPos pexp1) env{context = listToMaybe path0', resPath = path0'} (_exp pexp1) False
    return (IFunExp iJoin [pexp0{_exp=exp0'}, pexp1{_exp=exp1'}], path1')
  IClaferId modName' id' muid' _ -> if isFirst
    then mkPath env <$> resolveName pos' env (id', muid')
    else mkPath' modName' <$> resolveImmName pos' env (id', muid')
  y -> throwError $ SemanticErr pos' $ "Cannot resolve nav of " ++ show y 

-- depending on how resolved construct a path
mkPath :: SEnv -> (HowResolved, (UID, MUID), [IClafer]) -> (IExp, [IClafer])
mkPath env (howResolved, (id', muid'), path) = case howResolved of
  Binding -> (mkLClaferId id' muid' False, path)
  Special -> (specIExp, path)
  TypeSpecial -> (mkLClaferId id' muid' True, path)
  Subclafers -> (toNav $ tail zipPath, path)

  Ancestor -> (toNav' $ adjustAncestor zipResPath zipPath, path)
  _ -> (toNav' zipPath , path)
  where
  zipReveresePath :: [IClafer] -> [(UID, MUID)]
  zipReveresePath p = reverse $ zip (map _uid p) (map _claferMUID p)
  zipPath = zipReveresePath path
  zipResPath = zipReveresePath $ resPath env
  toNav = foldl'
          (\exp' (id'', muid'') -> IFunExp iJoin [pExpDefPidPos pseudoMUID exp', mkPLClaferId id'' muid'' False])
          (mkLClaferId thisIdent thisMUID True)
  specIExp = if id' /= thisIdent then toNav [(id', muid')] else mkLClaferId thisIdent thisMUID True

toNav' :: [(UID, MUID)] -> IExp
toNav' path = (mkIFunExp (pseudoMUID-1) iJoin $ map (\(cid, muid) -> mkLClaferId cid muid False) path) :: IExp


adjustAncestor :: [(UID, MUID)] -> [(UID, MUID)] -> [(UID, MUID)]
adjustAncestor cPath rPath = (thisIdent, thisMUID) : parents ++ (fromJust $ stripPrefix prefix rPath)
  where
  parents :: [(UID, MUID)]
  parents = replicate (length $ fromJust $ stripPrefix prefix cPath) (parentIdent, parentMUID)
  prefix :: [(UID, MUID)]
  prefix  = fst $ unzip $ takeWhile (uncurry (==)) $ zip cPath rPath


mkPath' :: String -> (HowResolved, (String, MUID), [IClafer]) -> (IExp, [IClafer])
mkPath'    _         (Reference,   (id', idMUID'), path)       = (toNav' [ (refIdent, refMUID), (id', idMUID') ], path)
mkPath'    modName'  (_        ,   (id', idMUID'), path)       = (IClaferId modName' id' idMUID' False, path)

-- -----------------------------------------------------------------------------

resolveName :: Span -> SEnv -> (UID, MUID) -> Resolve (HowResolved, (UID, MUID), [IClafer])
resolveName pos' env (id', muid') = resolve env (id', muid')
  [resolveSpecial, resolveBind, resolveDescendants, resolveAncestor pos', resolveTopLevel pos', resolveNone pos']


resolveImmName :: Span -> SEnv -> (UID, MUID) -> Resolve (HowResolved, (UID, MUID), [IClafer])
resolveImmName pos' env (id', muid') = resolve env (id', muid')
  [resolveSpecial, resolveChildren pos', resolveReference pos', resolveNone pos']


-- when one strategy fails, we want to move to the next one
resolve :: (Monad f, Functor f) => SEnv -> (UID, MUID) -> [SEnv -> (UID, MUID) -> f (Maybe b)] -> f b
resolve env (id', muid') fs = fromJust <$> (runMaybeT $ msum $ map (\x -> MaybeT $ x env (id', muid')) fs)


-- reports error if clafer not found
resolveNone :: Span -> SEnv -> (UID, MUID) -> Resolve t
resolveNone pos' env (id', _) =
  throwError $ SemanticErr pos' $ "Name resolver: '" ++ id' ++ "' not found" ++
  " within " ++ (showPath $ map _uid $ resPath env)


-- checks if ident is one of special identifiers
resolveSpecial :: SEnv -> (UID, MUID) -> Resolve (Maybe (HowResolved, (UID, MUID), [IClafer]))
resolveSpecial env (id', _)
  | id' == parentIdent = return $ Just (Special, (parentIdent, parentMUID), tail $ resPath env)  -- parent is also special, so need to check first
  | isSpecial id'      = return $ Just (Special, (id', getSpecialMUID id'), resPath env)
  | isPrimitive id'    = return $ Just (TypeSpecial, (id', getPrimitiveMUID id'), [])
  | otherwise          = return Nothing 


-- checks if ident is bound locally
resolveBind :: SEnv -> (UID, MUID) -> Resolve (Maybe (HowResolved, (UID, MUID), [IClafer]))
resolveBind env (id', _) = return $ find (\(locids, _) -> id' `elem` (fst $ unzip locids)) (bindings env) >>= createBinding
  where
    createBinding  (list, path) = Just (Binding, (id', fromJust $ lookup id' list), path)
    createBinding  rr = error $ "unmatched: " ++ show rr


-- searches for a name in all subclafers (BFS)
resolveDescendants :: SEnv -> (UID, MUID) -> Resolve (Maybe (HowResolved, (UID, MUID), [IClafer]))
resolveDescendants env (id', _) = return $
  (context env) >> (findFirst id' $ subClafers env) >>= (toMTriple Subclafers)


-- searches for a name in immediate subclafers (BFS)
resolveChildren :: Span -> SEnv -> (UID, MUID) -> Resolve (Maybe (HowResolved, (UID, MUID), [IClafer]))
resolveChildren pos' env (id', muid') = resolveChildren' pos' env (id', muid') allInhChildren Subclafers

-- searches for a name by dereferencing clafer
resolveReference :: Span -> SEnv -> (UID, MUID) -> Resolve (Maybe (HowResolved, (UID, MUID), [IClafer]))
resolveReference pos' env (id', muid') = resolveChildren' pos' env (id', muid') allChildren Reference

resolveChildren' :: Span -> SEnv -> (UID, MUID) -> (SEnv -> [IClafer]) -> HowResolved -> Either ClaferSErr (Maybe (HowResolved, (UID, MUID), [IClafer]))
resolveChildren' pos' env (id', muid') f label =
  runMaybeT $ do
    liftMaybe $ context env
    u <- MaybeT $ findUnique pos' (id', muid') $ map (\x -> (x, [x,fromJust $ context env])) $ f env
    liftMaybe $ toMTriple label u

liftMaybe :: Maybe a -> MaybeT (Either ClaferSErr) a
liftMaybe = MaybeT . return

resolveAncestor :: Span -> SEnv -> (UID, MUID) -> Resolve (Maybe (HowResolved, (UID, MUID), [IClafer]))
resolveAncestor pos' env (id', muid') =
  runMaybeT $ do
    liftMaybe $ context env
    u <- MaybeT $ findUnique pos' (id', muid') $ ancClafers env
    liftMaybe $ toMTriple Ancestor u


-- searches for a feature starting from local root (BFS) and then continues with
-- other declarations
resolveTopLevel :: Span -> SEnv -> (UID, MUID) -> Resolve (Maybe (HowResolved, (UID, MUID), [IClafer]))
resolveTopLevel pos' env (id', muid') = runMaybeT $ foldr1 mplus $ map
  (\(cs, hr) -> MaybeT (findUnique pos' (id', muid') cs) >>= (liftMaybe . toMTriple hr)) 
  [(aClafers env, AbsClafer), (cClafers env, TopClafer)]

toNodeDeep :: SEnv -> ((IClafer, [IClafer]), [SEnv])
              -- ((curr. clafer, resolution path), remaining children to traverse)
toNodeDeep env
  | length (clafer `elemIndices` resPath env) > 1 = (result, [])  -- cut bfs recusion in case clafer repeats
  | otherwise = (result, map (\c -> env {context = Just c,
                                         resPath = c : resPath env}) $
                 allInhChildren env)
  where
  result = (clafer, resPath env)
  clafer = fromJust $ context env
  

-- return children and inherited children but no children of reference targets
allInhChildren :: SEnv -> [IClafer]
allInhChildren = selectChildren getSuperNoArr

-- return all children including inherited children children of reference targets
allChildren :: SEnv -> [IClafer]
allChildren = selectChildren getSuper

selectChildren :: (IClafer -> String) -> SEnv -> [IClafer]
selectChildren f env = getSubclafers $ concat $
                       mapHierarchy _elements f (sClafers $ genv env)
                       (fromJust $ context env)

findUnique :: Span -> (String, MUID) -> [(IClafer, [IClafer])] -> Resolve (Maybe ((String, MUID), [IClafer]))
findUnique pos' (x, _) xs =
  case filterPaths x $ nub xs of
    []     -> return $ Nothing
    [(cl, cls)] -> return $ Just $ ((_uid cl, _claferMUID cl), cls)
    xs'    -> throwError $ SemanticErr pos' $ "clafer '" ++ show x ++ "' " ++ errMsg
      where
      xs''   = map ((map _uid).snd) xs'
      errMsg = (if isNamespaceConflict xs''
               then "cannot be defined because the name should be unique in the same namespace.\n"
               else "is not unique. ") ++ 
               "Available paths:\n" ++ (xs'' >>= showPath)

findFirst :: String -> [(IClafer, [IClafer])] -> Maybe ((String, MUID), [IClafer])
findFirst x xs =
  case filterPaths x $ nub xs of
    []       -> Nothing
    ((cl, cls):_) -> Just $ ((_uid cl, _claferMUID cl), cls)

showPath :: [String] -> String
showPath xs = (intercalate "." $ reverse xs) ++ "\n"

isNamespaceConflict :: [[String]] -> Bool
isNamespaceConflict (xs:ys:_) = tail xs == tail ys
isNamespaceConflict x         = error $ "isNamespaceConflict must be given a list"
                                         ++ " of at least two elements, but was given " ++ show x

filterPaths :: String -> [(IClafer, [IClafer])] -> [(IClafer, [IClafer])]
filterPaths x xs = filter (((==) x)._ident.fst) xs
