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
  bindings :: [([String], [IClafer])],  -- local names
  resPath :: [IClafer],                 -- path to the current clafer
  genv :: GEnv,                         -- (constant)
  aClafers :: [(IClafer, [IClafer])],   -- (constant) abstract clafers (BFS)
  cClafers :: [(IClafer, [IClafer])]    -- (constant) all concrete clafers (BFS)
  } deriving Show

-- | How a given name was resolved
data HowResolved =
  -- | "this", "parent", "children"
    Special     
  -- | primitive type: integer, string
  | TypeSpecial 
  -- | local variable (in constraints)
  | Binding     
  -- | clafer's descendant
  | Subclafers  
  -- | resolved by a reference
  | Reference   
  -- | clafer's ancestor
  | Ancestor    
  -- | abstract clafer
  | AbsClafer   
  -- | non-abstract top-level clafer
  | TopClafer   
  deriving (Eq, Show)
  
type Resolve = Either ClaferSErr

-- initialize the cache (env)
defSEnv :: GEnv -> [IElement] -> SEnv
defSEnv genv' declarations = env {aClafers = rCl aClafers',
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
  IEConstraint isHard' pexp  -> IEConstraint isHard' <$> resolvePExp env pexp
  IEGoal isMaximize' pexp  -> IEGoal isMaximize' <$> resolvePExp env pexp  


resolvePExp :: SEnv -> PExp -> Resolve PExp
resolvePExp env pexp =
  do
    exp' <- resolveIExp (_inPos pexp) env $ Language.Clafer.Intermediate.Intclafer._exp pexp
    return $ pexp {Language.Clafer.Intermediate.Intclafer._exp = exp'}

resolveIExp :: Span -> SEnv -> IExp -> Resolve IExp
resolveIExp pos' env x = case x of
  IDeclPExp quant' decls' pexp -> do
    let (decls'', env') = runState (runErrorT $ (mapM (ErrorT . processDecl) decls')) env
    IDeclPExp quant' <$> decls'' <*> resolvePExp env' pexp

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
  env <- lift $ get
  (body', path) <- liftError $ resolveNav (_inPos $ _body decl) env (I._exp $ _body decl) True
  lift $ modify (\e -> e { bindings = (_decls decl, path) : bindings e })
  return $ decl {_body = pExpDefPidPos body'}

resolveNav :: Span -> SEnv -> IExp -> Bool -> Resolve (IExp, [IClafer])
resolveNav pos' env x isFirst = case x of
  IFunExp _ (pexp0:pexp:_) -> do
    (exp0', path) <- resolveNav (_inPos pexp0) env (I._exp pexp0) True
    (exp', path') <- resolveNav (_inPos pexp) env {context = listToMaybe path, resPath = path}
                     (I._exp pexp) False
    return (IFunExp iJoin [pexp0{I._exp=exp0'}, pexp{I._exp=exp'}], path')
  IClaferId modName' id' _ _-> out
    where
    out
      | isFirst   = mkPath env <$> resolveName pos' env id'
      | otherwise = mkPath' modName' <$> resolveImmName pos' env id'
  y -> throwError $ SemanticErr pos' $ "Cannot resolve nav of " ++ show y 

-- depending on how resolved construct a path
mkPath :: SEnv -> (HowResolved, String, [IClafer]) -> (IExp, [IClafer])
mkPath env (howResolved, id', path) = case howResolved of
  Binding -> (mkLClaferId id' True Nothing, path)
  Special -> (specIExp, path)
  TypeSpecial -> (mkLClaferId id' True Nothing, path)
  Subclafers -> (toNav $ tail $ reverse $ map toTuple path, path)
  Ancestor -> (toNav' $ adjustAncestor (fromJust $ context env)
                                       (reverse $ map toTuple $ resPath env)
                                       (reverse $ map toTuple path), path)
  _ -> (toNav' $ reverse $ map toTuple path, path)
  where
  toNav = foldl'
          (\exp' (id'', c) -> IFunExp iJoin [pExpDefPidPos exp', mkPLClaferId id'' False $ _uid <$> c])
          (mkLClaferId this True (_uid <$> context env))
  specIExp = if id' /= this then toNav [(id', Just $ head path)] else mkLClaferId id' True (_uid <$> context env)

toTuple :: IClafer->(String, Maybe IClafer)
toTuple c = (_uid c, Just c)

toNav' :: [(String, Maybe IClafer)] -> IExp
toNav' p = (mkIFunExp iJoin $ map (\(id', cbind) -> mkLClaferId id' False (_uid <$> cbind)) p) :: IExp


adjustAncestor :: IClafer -> [(String, Maybe IClafer)] -> [(String, Maybe IClafer)] -> [(String, Maybe IClafer)]
adjustAncestor ctx cPath rPath = (this, Just ctx) : parents ++ (fromJust $ stripPrefix prefix rPath)
  where
  parents = replicate (length $ fromJust $ stripPrefix prefix cPath) (parent, Nothing)
  prefix = fst $ unzip $ takeWhile (uncurry eqIds) $ zip cPath rPath
  eqIds a b = (fst a) == (fst b)


mkPath' :: String -> (HowResolved, String, [IClafer]) -> (IExp, [IClafer])
mkPath' modName' (howResolved, id', path) = case howResolved of
  Reference -> (toNav' (zip ["ref", id'] (map Just path)), path)
  _ -> (IClaferId modName' id' False (_uid <$> bind), path)
  where
  bind = case path of
    [] -> Nothing
    c:_ -> Just c

-- -----------------------------------------------------------------------------

resolveName :: Span -> SEnv -> String -> Resolve (HowResolved, String, [IClafer])
resolveName pos' env id' = resolve env id'
  [resolveSpecial, resolveBind, resolveDescendants, resolveAncestor pos', resolveTopLevel pos', resolveNone pos']


resolveImmName :: Span -> SEnv -> String -> Resolve (HowResolved, String, [IClafer])
resolveImmName pos' env id' = resolve env id'
  [resolveSpecial, resolveChildren pos', resolveReference pos', resolveNone pos']


-- when one strategy fails, we want to move to the next one
resolve :: (Monad f, Functor f) => SEnv -> String -> [SEnv -> String -> f (Maybe b)] -> f b
resolve env id' fs = fromJust <$> (runMaybeT $ msum $ map (\x -> MaybeT $ x env id') fs)


-- reports error if clafer not found
resolveNone :: Span -> SEnv -> String -> Resolve t
resolveNone pos' env id' =
  throwError $ SemanticErr pos' $ "resolver: " ++ id' ++ " not found" ++
  " within " ++ (showPath $ map _uid $ resPath env)


-- checks if ident is one of special identifiers
resolveSpecial :: SEnv -> String -> Resolve (Maybe (HowResolved, String, [IClafer]))
resolveSpecial env id'
  | id' `elem` [this, children, ref] =
      return $ Just (Special, id', resPath env)
  | id' == parent   = return $ Just (Special, id', tail $ resPath env)
  | isPrimitive id' = return $ Just (TypeSpecial, id', [])
  | otherwise      = return Nothing 


-- checks if ident is bound locally
resolveBind :: SEnv -> String -> Resolve (Maybe (HowResolved, String, [IClafer]))
resolveBind env id' = return $ find (\bs -> id' `elem` fst bs) (bindings env) >>=
  (\x -> Just (Binding, id', snd x))


-- searches for a name in all subclafers (BFS)
resolveDescendants :: SEnv -> String -> Resolve (Maybe (HowResolved, String, [IClafer]))
resolveDescendants env id' = return $
  (context env) >> (findFirst id' $ subClafers env) >>= (toMTriple Subclafers)


-- searches for a name in immediate subclafers (BFS)
resolveChildren :: Span -> SEnv -> String -> Resolve (Maybe (HowResolved, String, [IClafer]))
resolveChildren pos' env id' = resolveChildren' pos' env id' allInhChildren Subclafers

-- searches for a name by dereferencing clafer
resolveReference :: Span -> SEnv -> String -> Resolve (Maybe (HowResolved, String, [IClafer]))
resolveReference pos' env id' = resolveChildren' pos' env id' allChildren Reference

resolveChildren' :: Span -> SEnv -> String -> (SEnv -> [IClafer]) -> HowResolved -> Either ClaferSErr (Maybe (HowResolved, String, [IClafer]))
resolveChildren' pos' env id' f label =
  runMaybeT $ do
    liftMaybe $ context env
    u <- MaybeT $ findUnique pos' id' $ map (\x -> (x, [x,fromJust $ context env])) $ f env
    liftMaybe $ toMTriple label u

liftMaybe :: Maybe a -> MaybeT (Either ClaferSErr) a
liftMaybe = MaybeT . return

resolveAncestor :: Span -> SEnv -> String -> Resolve (Maybe (HowResolved, String, [IClafer]))
resolveAncestor pos' env id' =
  runMaybeT $ do
    liftMaybe $ context env
    u <- MaybeT $ findUnique pos' id' $ ancClafers env
    liftMaybe $ toMTriple Ancestor u


-- searches for a feature starting from local root (BFS) and then continues with
-- other declarations
resolveTopLevel :: Span -> SEnv -> String -> Resolve (Maybe (HowResolved, String, [IClafer]))
resolveTopLevel pos' env id' = runMaybeT $ foldr1 mplus $ map
  (\(cs, hr) -> MaybeT (findUnique pos' id' cs) >>= (liftMaybe . toMTriple hr))
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

findUnique :: Span -> String -> [(IClafer, [IClafer])] -> Resolve (Maybe (String, [IClafer]))
findUnique pos' x xs =
  case filterPaths x $ nub xs of
    []     -> return $ Nothing
    [elem'] -> return $ Just $ (_uid $ fst elem', snd elem')
    xs'    -> throwError $ SemanticErr pos' $ "clafer " ++ show x ++ " " ++ errMsg
      where
      xs''   = map ((map _uid).snd) xs'
      errMsg = (if isNamespaceConflict xs''
               then "cannot be defined because the name should be unique in the same namespace.\n"
               else "is not unique. ") ++ 
               "Available paths:\n" ++ (xs'' >>= showPath)

findFirst :: String -> [(IClafer, [IClafer])] -> Maybe (String, [IClafer])
findFirst x xs =
  case filterPaths x $ nub xs of
    []       -> Nothing
    (ele:_) -> Just $ (_uid $ fst ele, snd ele)

showPath :: [String] -> String
showPath xs = (intercalate "." $ reverse xs) ++ "\n"

isNamespaceConflict :: [[String]] -> Bool
isNamespaceConflict (xs:ys:_) = tail xs == tail ys
isNamespaceConflict x         = error $ "isNamespaceConflict must be given a list"
                                         ++ " of at least two elements, but was given " ++ show x

filterPaths :: String -> [(IClafer, [IClafer])] -> [(IClafer, [IClafer])]
filterPaths x xs = filter (((==) x)._ident.fst) xs
