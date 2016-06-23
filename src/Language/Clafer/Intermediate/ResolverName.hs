{-# LANGUAGE FlexibleContexts #-}

{-
 Copyright (C) 2012 Kacper Bak, Jimmy Liang, Michal Antkiewicz <http://gsd.uwaterloo.ca>

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
import Control.Monad.Except
import Control.Monad.Trans.Maybe
import Control.Monad.State
import Data.Maybe
import Data.Function
import Data.List
import Prelude

import Language.ClaferT
import Language.Clafer.Common
import Language.Clafer.Intermediate.Intclafer

-- | this environment is created for each clafer
data SEnv
  = SEnv
  { clafers :: [IClafer]                 -- (constant) top level clafers
  , context :: Maybe IClafer             -- context of a constraint
  , subClafers :: [(IClafer, [IClafer])] -- descendans (BFS)
  , ancClafers :: [(IClafer, [IClafer])] -- ancesors (BFS)
  , bindings :: [([String], [IClafer])]  -- local names
  , resPath :: [IClafer]                 -- path to the current clafer
  , genv :: GEnv                         -- (constant)
  , aClafers :: [(IClafer, [IClafer])]   -- (constant) abstract clafers (BFS)
  , cClafers :: [(IClafer, [IClafer])]   -- (constant) all concrete clafers (BFS)
  } deriving Show

-- | How a given name was resolved
data HowResolved
  = Special     -- ^ "this", "parent", "dref", "root", "clafer", and "children"
  | TypeSpecial -- ^ primitive type: "integer", "string"
  | Binding     -- ^ local variable (in constraints)
  | Subclafers  -- ^ clafer's descendant
  | Reference   -- ^ resolved by a reference
  | Ancestor    -- ^ clafer's ancestor
  | AbsClafer   -- ^ abstract clafer
  | TopClafer   -- ^ non-abstract top-level clafer
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
resolveModuleNames    (imodule, genv') =
  do
    decls' <- checkDuplicateSiblings imodule
    let defaultSEnv = defSEnv genv' decls'
    mDecls' <- mapM (resolveElement defaultSEnv) decls'
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

resolvePExp :: SEnv -> PExp                          -> Resolve PExp
resolvePExp    env     pexp@PExp{_exp=x} = case x of
  IDeclPExp quant' decls' pexp2 -> do
    let (decls'', env') = runState (runExceptT $ (mapM (ExceptT . processDecl) decls')) env
    exp' <- IDeclPExp quant' <$> decls'' <*> resolvePExp env' pexp2
    return pexp{_exp=exp'}

  IFunExp "." _ -> fst <$> resolveNav env pexp True
  IFunExp op' exps' -> do
                         exp' <- IFunExp op' <$> mapM (resolvePExp env) exps'
                         return $ pexp {_exp = exp'}
  IInt _ -> return pexp
  IDouble _ -> return pexp
  IReal _ -> return pexp
  IStr _ -> return pexp
  IClaferId{} -> fst <$> resolveNav env pexp True

liftError :: Monad m => Either e a -> ExceptT e m a
liftError = ExceptT . return

processDecl :: MonadState SEnv m => IDecl -> m (Resolve IDecl)
processDecl decl = runExceptT $ do
  env <- lift $ get
  (body', path) <- liftError $ resolveNav env (_body decl) True
  lift $ modify (\e -> e { bindings = (_decls decl, path) : bindings e })
  return $ decl {_body = body'}

resolveNav :: SEnv -> PExp                         -> Bool   -> Resolve (PExp, [IClafer])
resolveNav    env     pexp0@PExp{_inPos=pos', _exp=x} isFirst = case x of
  IFunExp "." [pexp1,pexp2] -> do
    (pexp1', path1) <- resolveNav env                                               pexp1 True
    (pexp2', path2) <- resolveNav env{context = listToMaybe path1, resPath = path1} pexp2 False
    -- if `dref` was added to the RHS we need to left rotate the tree
    case pexp2' of
      PExp{_exp=IFunExp "." [pexp2'l, pexp2'r]} -> (case pexp2'l of
        PExp{_exp=IClaferId{_sident="dref"}} ->
          let -- move the `dref` to the LHS
            pexp0' = pexp0{_exp=IFunExp iJoin [pexp1', pexp2'l]}
          in -- keep the RHS as is
            return (pexp2{_exp=IFunExp iJoin [pexp0', pexp2'r]}, path2)
        _ -> return (pexp0{_exp=IFunExp iJoin [pexp1', pexp2']}, path2)
        )
      _ -> return (pexp0{_exp=IFunExp iJoin [pexp1', pexp2']}, path2)
  IClaferId modName' id' _ _ -> if isFirst
    then do
           (exp', path') <- mkPath pos' env <$> resolveName pos' env id'
           return (pexp0{_exp=exp'}, path')
    else do
           (exp', path') <- mkPath' pos' modName' <$> resolveImmName pos' env id'
           return (pexp0{_exp=exp'}, path')
  y -> throwError $ SemanticErr pos' $ "Cannot resolve nav of " ++ show y

-- | Depending on how resolved construct a navigation path from 'context env'
mkPath :: Span -> SEnv -> (HowResolved, String, [IClafer]) -> (IExp, [IClafer])
mkPath    pos'    env     (howResolved, id',    path)       = case howResolved of
  Binding -> (IClaferId "" id' True Nothing, path)
  Special -> (specIExp id', path)
  TypeSpecial -> (IClaferId "" id' True (Just id'), path)
  Subclafers -> (toNav $ tail $ reverse $ map toTuple path, path)
  Ancestor -> (toNav' pos' $ adjustAncestor (fromJust $ context env)
                                       (reverse $ map toTuple $ resPath env)
                                       (reverse $ map toTuple path), path)
  Reference -> (toNav' pos' $ reverse $ map toTuple path, path)
  AbsClafer -> (toNav' pos' $ reverse $ map toTuple path, path)
  TopClafer -> (toNav' pos' $ reverse $ map toTuple path, path)
  where
  toNav tuplePath = foldl'
          (\exp' (id'', cbind) -> IFunExp iJoin [pExpDefPid pos' exp', mkPLClaferId pos' id'' (fromMaybe False $ isTopLevel <$> cbind) $ _uid <$> cbind])
          (IClaferId "" thisIdent True (_uid <$> context env))
          tuplePath
  specIExp "this"     = IClaferId "" thisIdent True (_uid <$> context env)
  specIExp "parent"   = toNav [("parent", Just $ head path)]
  specIExp "dref"     = toNav [("dref", Just $ head path)]
  specIExp "root"     = IClaferId "" rootIdent True (Just rootIdent)
  specIExp "children" = toNav [(id', Just $ head path)]
  specIExp i          = error $ "[BUG] ResolverName.specIExp: Unknown special id: " ++ i

toTuple :: IClafer->(String, Maybe IClafer)
toTuple c = (_uid c, Just c)

toNav' :: Span -> [(String, Maybe IClafer)] -> IExp
toNav'    pos'    tuplePath                  =
  (mkIFunExp pos' iJoin $ map (\(id', cbind) -> IClaferId "" id' (fromMaybe False $ isTopLevel <$> cbind) (_uid <$> cbind)) tuplePath) :: IExp

adjustAncestor :: IClafer -> [(String, Maybe IClafer)] -> [(String, Maybe IClafer)] -> [(String, Maybe IClafer)]
adjustAncestor ctx cPath rPath = (thisIdent, Just ctx) : parents ++ (fromJust $ stripPrefix prefix rPath)
  where
  parents = replicate (length $ fromJust $ stripPrefix prefix cPath) (parentIdent, Nothing)
  prefix = fst $ unzip $ takeWhile (uncurry eqIds) $ zip cPath rPath
  eqIds a b = (fst a) == (fst b)


mkPath' :: Span -> String -> (HowResolved, String, [IClafer]) -> (IExp, [IClafer])
mkPath'    pos' modName'  (howResolved, id', path)          = case howResolved of
  Reference -> (toNav' pos' (zip ["dref", id'] (map Just path)), path)
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
resolve :: Monad f => SEnv -> String -> [SEnv -> String -> f (Maybe b)] -> f b
resolve env id' fs = fromJust <$> (runMaybeT $ msum $ map (\x -> MaybeT $ x env id') fs)


-- reports error if clafer not found
resolveNone :: Span -> SEnv -> String -> Resolve t
resolveNone pos' env id' =
  throwError $ SemanticErr pos' $ concat
    [ "Name resolver: '"
    , id'
    , "' not found within paths:"
    , showPath $ map _uid $ resPath env
    , "in context of '"
    , show $ fromMaybe "none" (_uid <$> context env)
    , "'" ]


-- checks if ident is one of special identifiers
resolveSpecial :: SEnv -> String -> Resolve (Maybe (HowResolved, String, [IClafer]))
resolveSpecial env id'
  | id' == parentIdent = return $ Just (Special, id', safeTail $ resPath env)
  | isSpecial id'      = return $ Just (Special, id', resPath env)
  | isPrimitive id'    = return $ Just (TypeSpecial, id', [])
  | otherwise          = return Nothing


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
resolveChildren' pos' env id' getChildrenF label =
  runMaybeT $ do
    _ <- liftMaybe $ context env
    u <- MaybeT $ findUnique pos' id' $ map (\x -> (x, [x,fromJust $ context env])) $ getChildrenF env
    liftMaybe $ toMTriple label u

liftMaybe :: Maybe a -> MaybeT (Either ClaferSErr) a
liftMaybe = MaybeT . return

resolveAncestor :: Span -> SEnv -> String -> Resolve (Maybe (HowResolved, String, [IClafer]))
resolveAncestor pos' env id' =
  runMaybeT $ do
    _ <- liftMaybe $ context env
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
allInhChildren = selectChildren getSuper

-- return all children including inherited children children of reference targets
allChildren :: SEnv -> [IClafer]
allChildren = selectChildren getSuperAndReference

selectChildren :: (IClafer -> [String]) -> SEnv -> [IClafer]
selectChildren f env = getSubclafers $ concat $
                       mapHierarchy _elements f (uidClaferMap $ genv env)
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
