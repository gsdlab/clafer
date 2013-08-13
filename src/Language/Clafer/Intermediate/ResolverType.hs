{-# LANGUAGE NamedFieldPuns, ScopedTypeVariables, FlexibleContexts, FlexibleInstances, UndecidableInstances, GeneralizedNewtypeDeriving #-}

{-
 Copyright (C) 2012 Jimmy Liang, Kacper Bak <http://gsd.uwaterloo.ca>

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
module Language.Clafer.Intermediate.ResolverType (resolveTModule, intersects, (+++), fromUnionType, unionType)  where

import Prelude hiding (exp)
import Language.ClaferT
import Language.Clafer.Common
import Language.Clafer.Intermediate.Analysis
import Language.Clafer.Intermediate.Intclafer hiding (uid)
import qualified Language.Clafer.Intermediate.Intclafer as I

import Control.Applicative
import Control.Monad.Error
import Control.Monad.List
import Control.Monad.Reader
import Data.Either
import Data.List
import Data.Maybe

type TypeDecls = [(String, IType)]
data TypeInfo = TypeInfo {iTypeDecls::TypeDecls, iInfo::Info, iCurThis::SClafer, iCurPath::Maybe IType}

newtype TypeAnalysis a = TypeAnalysis (ReaderT TypeInfo (Either ClaferSErr) a)
  deriving (MonadError ClaferSErr, Monad, Functor, MonadReader TypeInfo)
  
typeOfUid :: MonadTypeAnalysis m => String -> m IType
typeOfUid uid = (fromMaybe (TClafer [uid]) . lookup uid) <$> typeDecls

class MonadAnalysis m => MonadTypeAnalysis m where
  -- What "this" refers to
  curThis :: m SClafer
  localCurThis :: SClafer -> m a -> m a
  
  -- The next path is a child of curPath (or Nothing)
  curPath :: m (Maybe IType)
  localCurPath :: IType -> m a -> m a
  
  -- Extra declarations
  typeDecls :: m TypeDecls
  localDecls :: TypeDecls -> m a -> m a

instance MonadTypeAnalysis TypeAnalysis where
  curThis = TypeAnalysis $ asks iCurThis
  localCurThis newThis (TypeAnalysis d) =
    TypeAnalysis $ local setCurThis d
    where
    setCurThis t = t{iCurThis = newThis}
    
  curPath = TypeAnalysis $ asks iCurPath
  localCurPath newPath (TypeAnalysis d) =
    TypeAnalysis $ local setCurPath d
    where
    setCurPath t = t{iCurPath = Just newPath}
    
  typeDecls = TypeAnalysis $ asks iTypeDecls
  localDecls extra (TypeAnalysis d) =
    TypeAnalysis $ local addTypeDecls d
    where
    addTypeDecls t@TypeInfo{iTypeDecls = c} = t{iTypeDecls = extra ++ c}
    
instance MonadTypeAnalysis m => MonadTypeAnalysis (ListT m) where
  curThis = lift $ curThis
  localCurThis = mapListT . localCurThis
  curPath = lift $ curPath
  localCurPath = mapListT . localCurPath
  typeDecls = lift typeDecls
  localDecls = mapListT . localDecls
  
instance MonadTypeAnalysis m => MonadTypeAnalysis (ErrorT ClaferSErr m) where
  curThis = lift $ curThis
  localCurThis = mapErrorT . localCurThis
  curPath = lift $ curPath
  localCurPath = mapErrorT . localCurPath
  typeDecls = lift typeDecls
  localDecls = mapErrorT . localDecls
      

instance MonadAnalysis TypeAnalysis where
  clafers = asks (sclafers . iInfo)
  withClafers cs r =
    local setInfo r
    where
    setInfo t = t{iInfo = Info cs}

runTypeAnalysis :: TypeAnalysis a -> IModule -> Either ClaferSErr a
runTypeAnalysis (TypeAnalysis tc) imodule = runReaderT tc $ TypeInfo [] (gatherInfo imodule) undefined Nothing

unionType :: IType -> [String]
unionType TString  = ["string"]
unionType TReal    = ["real"]
unionType TInteger = ["integer"]
unionType TBoolean = ["boolean"]
unionType (TClafer u) = u

(+++) :: IType -> IType -> IType
t1 +++ t2 = fromJust $ fromUnionType $ unionType t1 ++ unionType t2

fromUnionType :: [String] -> Maybe IType
fromUnionType u =
    case sort $ nub $ u of
        ["string"]  -> return TString
        ["real"]    -> return TReal
        ["integer"] -> return TInteger
        ["int"]     -> return TInteger
        ["boolean"] -> return TBoolean
        []          -> Nothing
        u'          -> return $ TClafer u'

closure :: MonadAnalysis m => [String] -> m [String]
closure ut = concat <$> mapM hierarchy ut

intersection :: MonadAnalysis m => IType -> IType -> m (Maybe IType)
intersection t1 t2 = 
  do
    h1 <- mapM hierarchy $ unionType t1
    h2 <- mapM hierarchy $ unionType t2
    let ut = catMaybes [contains (head u1) u2 `mplus` contains (head u2) u1 | u1 <- h1, u2 <- h2]
    return $ fromUnionType ut
  where
  contains i is = if i `elem` is then Just i else Nothing

intersects :: MonadAnalysis m => IType -> IType -> m Bool
intersects t1 t2 = isJust <$> intersection t1 t2

numeric :: IType -> Bool
numeric TReal    = True
numeric TInteger = True
numeric _        = False

coerce :: IType -> IType -> IType
coerce TReal TReal       = TReal
coerce TReal TInteger    = TReal
coerce TInteger TReal    = TReal
coerce TInteger TInteger = TInteger
coerce x y = error $ "Not numeric: " ++ show x ++ ", " ++ show y

str :: IType -> String
str t =
  case unionType t of
    [t'] -> t'
    ts   -> "[" ++ intercalate "," ts ++ "]"

getIfThenElseType :: MonadAnalysis m => IType -> IType -> m (Maybe IType)
-- the function is similar to 'intersection', but takes into account more ancestors to be able to combine
-- clafers of different types, but with a common ancestor:
-- Inputs:
-- t1 is of type B
-- t2 is of type C
-- B : A
-- C : A
-- Outputs:
-- the resulting type is: A, and the type combination is valid
getIfThenElseType t1 t2 = 
  do
    h1 <- mapM hierarchy $ unionType t1
    h2 <- mapM hierarchy $ unionType t2
    let ut = catMaybes [commonHierarchy u1 u2 | u1 <- h1, u2 <- h2]
    return $ fromUnionType ut
  where
  commonHierarchy h1 h2 = filterClafer $ commonHierarchy' (reverse h1) (reverse h2) Nothing
  commonHierarchy' (x:xs) (y:ys) accumulator = 
    if (x == y) 
      then 
        if (null xs || null ys) 
          then Just x
          else commonHierarchy' xs ys $ Just x 
      else accumulator
  commonHierarchy' _ _ _ = error "Function commonHierarchy' from ResolverType expects two non empty lists but was given at least one empty list!" -- Should never happen    
  filterClafer value = 
    if (value == Just "clafer") then Nothing else value

resolveTModule :: (IModule, GEnv) -> Either ClaferSErr IModule
resolveTModule (imodule, _) =
  case runTypeAnalysis (analysis $ mDecls imodule) imodule of
    Right mDecls' -> return imodule{mDecls = mDecls'}
    Left err      -> throwError err
  where
  analysis decls = mapM (resolveTElement $ rootUid) decls

resolveTElement :: String -> IElement -> TypeAnalysis IElement
resolveTElement _ (IEClafer iclafer) =
  do
    elements' <- mapM (resolveTElement $ I.uid iclafer) (elements iclafer)
    return $ IEClafer $ iclafer{elements = elements'}
resolveTElement parent' (IEConstraint isHard pexp) =
  IEConstraint isHard <$> (testBoolean =<< resolveTConstraint parent' pexp)
  where
  testBoolean pexp' =
    do
      unless (typeOf pexp' == TBoolean) $
        throwError $ SemanticErr (inPos pexp') ("Cannot construct constraint on type '" ++ str (typeOf pexp') ++ "'")
      return pexp'
resolveTElement parent' (IEGoal isMaximize pexp) =
  IEGoal isMaximize <$> resolveTConstraint parent' pexp

resolveTConstraint :: String -> PExp -> TypeAnalysis PExp
resolveTConstraint curThis' constraint = 
  do
    curThis'' <- claferWithUid curThis'
    head <$> (localCurThis curThis'' $ (resolveTPExp constraint :: TypeAnalysis [PExp]))
    

resolveTPExp :: PExp -> TypeAnalysis [PExp]
resolveTPExp p = 
  do
    x <- resolveTPExp' p
    case partitionEithers x of
      (f:_, []) -> throwError f                       -- Case 1: Only fails. Complain about the first one.
      ([], [])  -> error "No results but no errors."  -- Case 2: No success and no error message. Bug.
      (_,   xs) -> return xs                          -- Case 3: At least one success.

resolveTPExp' :: PExp -> TypeAnalysis [Either ClaferSErr PExp]
resolveTPExp' p@PExp{inPos, exp = IClaferId{sident = "ref"}} =
  runListT $ runErrorT $ do
    curPath' <- curPath
    case curPath' of
      Just curPath'' -> do
        ut <- closure $ unionType curPath''
        t <- runListT $ refOf =<< foreachM ut
        case fromUnionType t of
          Just t' -> return $ p `withType` t'
          Nothing -> throwError $ SemanticErr inPos ("Cannot ref from type '" ++ str curPath'' ++ "'")
      Nothing -> throwError $ SemanticErr inPos ("Cannot ref at the start of a path")
resolveTPExp' p@PExp{inPos, exp = IClaferId{sident = "parent"}} =
  runListT $ runErrorT $ do
    curPath' <- curPath
    case curPath' of
      Just curPath'' -> do
        parent' <- fromUnionType <$> runListT (parentOf =<< liftList (unionType curPath''))
        when (isNothing parent') $
          throwError $ SemanticErr inPos "Cannot parent from root"
        let result = p `withType` fromJust parent'
        return result -- Case 1: Use the sident
          <++>
          addRef result -- Case 2: Dereference the sident 1..* times
      Nothing -> throwError $ SemanticErr inPos "Cannot parent at the start of a path"
resolveTPExp' p@PExp{exp = IClaferId{sident = "integer"}} = runListT $ runErrorT $ return $ p `withType` TInteger
resolveTPExp' p@PExp{inPos, exp = IClaferId{sident}} = 
  runListT $ runErrorT $ do
    curPath' <- curPath
    sident' <- if sident == "this" then uid <$> curThis else return sident
    when (isJust curPath') $ do
      c <- mapM (isChild sident') $ unionType $ fromJust curPath'
      unless (or c) $ throwError $ SemanticErr inPos ("'" ++ sident' ++ "' is not a child of type '" ++ str (fromJust curPath') ++ "'")
    result <- (p `withType`) <$> typeOfUid sident'
    return result -- Case 1: Use the sident
      <++>
      addRef result -- Case 2: Dereference the sident 1..* times
  
  
resolveTPExp' p@PExp{inPos, exp} =
  runListT $ runErrorT $ do
    (iType', exp') <- ErrorT $ ListT $ resolveTExp exp
    return p{iType = Just iType', exp = exp'}
  where
  resolveTExp :: IExp -> TypeAnalysis [Either ClaferSErr (IType, IExp)]
  resolveTExp e@(IInt _)    = runListT $ runErrorT $ return (TInteger, e)
  resolveTExp e@(IDouble _) = runListT $ runErrorT $ return (TReal, e)
  resolveTExp e@(IStr _)    = runListT $ runErrorT $ return (TString, e)

  resolveTExp e@IFunExp {op, exps = [arg]} =
    runListT $ runErrorT $ do
      arg' <- lift $ ListT $ resolveTPExp arg
      let t = typeOf arg'
      let test c =
            unless c $
              throwError $ SemanticErr inPos ("Function '" ++ op ++ "' cannot be performed on " ++ op ++ " '" ++ str t ++ "'")
      let result
            | op == iNot = test (t == TBoolean) >> return TBoolean
            | op == iCSet = return TInteger
            | op == iSumSet = test (t == TInteger) >> return TInteger
            | op `elem` [iMin, iGMin, iGMax] = test (numeric t) >> return t
            | otherwise = error $ "Unknown op '" ++ op ++ "'"
      result' <- result
      return (result', e{exps = [arg']})

  resolveTExp e@IFunExp {op = ".", exps = [arg1, arg2]} =
    do
      runListT $ runErrorT $ do
        arg1' <- lift $ ListT $ resolveTPExp arg1
        localCurPath (typeOf arg1') $ do
            arg2' <- liftError $ lift $ ListT $ resolveTPExp arg2
            return (fromJust $ iType arg2', e{exps = [arg1', arg2']})
      
  resolveTExp e@IFunExp {op = "++", exps = [arg1, arg2]} =
    do
      arg1s' <- resolveTPExp arg1
      arg2s' <- resolveTPExp arg2
      let union' a b = typeOf a +++ typeOf b
      return $ [return (union' arg1' arg2', e{exps = [arg1', arg2']}) | (arg1', arg2') <- sortBy (comparing $ uncurry union') $ liftM2 (,) arg1s' arg2s']
  resolveTExp e@IFunExp {op, exps = [arg1, arg2]} =
    runListT $ runErrorT $ do
      arg1' <- lift $ ListT $ resolveTPExp arg1
      arg2' <- lift $ ListT $ resolveTPExp arg2
      let t1 = typeOf arg1'
      let t2 = typeOf arg2'
      let testIntersect e1 e2 =
            do
              it <- intersection e1 e2
              case it of
                Just it' -> return it'
                Nothing  -> throwError $ SemanticErr inPos ("Function '" ++ op ++ "' cannot be performed on '" ++ str t1 ++ "' " ++ op ++ " '" ++ str t2 ++ "'")
      let testNotSame e1 e2 =
            when (e1 `sameAs` e2) $
              throwError $ SemanticErr inPos ("Function '" ++ op ++ "' is redundant because the two subexpressions are always equivalent")
      let test c =
            unless c $
              throwError $ SemanticErr inPos ("Function '" ++ op ++ "' cannot be performed on '" ++ str t1 ++ "' " ++ op ++ " '" ++ str t2 ++ "'")
      let result
            | op `elem` logBinOps = test (t1 == TBoolean && t2 == TBoolean) >> return TBoolean
            | op `elem` [iLt, iGt, iLte, iGte] = test (numeric t1 && numeric t2) >> return TBoolean
            | op `elem` [iEq, iNeq] = testNotSame arg1' arg2' >> testIntersect t1 t2 >> return TBoolean
            | op == iDifference = testNotSame arg1' arg2' >> testIntersect t1 t2 >> return t1
            | op == iIntersection = testNotSame arg1' arg2' >> testIntersect t1 t2
            | op `elem` [iDomain, iRange] = testIntersect t1 t2
            | op `elem` relSetBinOps = testIntersect t1 t2 >> return TBoolean
            | op `elem` [iSub, iMul, iDiv] = test (numeric t1 && numeric t2) >> return (coerce t1 t2)
            | op == iPlus =
                (test (t1 == TString && t2 == TString) >> return TString) -- Case 1: String concatenation
                `catchError`
                const (test (numeric t1 && numeric t2) >> return (coerce t1 t2)) -- Case 2: Addition
            | otherwise = error $ "Unknown op: " ++ show e
      result' <- result
      return (result', e{exps = [arg1', arg2']})

  resolveTExp e@(IFunExp "=>else" [arg1, arg2, arg3]) =
    runListT $ runErrorT $ do
      arg1' <- lift $ ListT $ resolveTPExp arg1
      arg2' <- lift $ ListT $ resolveTPExp arg2
      arg3' <- lift $ ListT $ resolveTPExp arg3
      let t1 = typeOf arg1'
      let t2 = typeOf arg2'
      let t3 = typeOf arg3'
--      unless (False) $
--        throwError $ SemanticErr inPos ("The types are: '" ++ str t2 ++ "' and '" ++ str t3 ++ "'")

      unless (t1 == TBoolean) $
        throwError $ SemanticErr inPos ("Function 'if/else' cannot be performed on 'if' " ++ str t1 ++ " 'then' " ++ str t2 ++ " 'else' " ++ str t3)

      it <- getIfThenElseType t2 t3
      t <- case it of
        Just it' -> return it'
        Nothing  -> throwError $ SemanticErr inPos ("Function '=>else' cannot be performed on if '" ++ str t1 ++ "' then '" ++ str t2 ++ "' else '" ++ str t3 ++ "'")

      return (t, e{exps = [arg1', arg2', arg3']})
      
  resolveTExp e@IDeclPExp{oDecls, bpexp} =
    runListT $ runErrorT $ do
      oDecls' <- mapM resolveTDecl oDecls
      let extraDecls = [(decl, typeOf $ body oDecl) | oDecl <- oDecls', decl <- decls oDecl]
      localDecls extraDecls $ do
        bpexp' <- liftError $ lift $ ListT $ resolveTPExp bpexp
        return $ (TBoolean, e{oDecls = oDecls', bpexp = bpexp'})
    where
    resolveTDecl d@IDecl{body} =
      do
        body' <- lift $ ListT $ resolveTPExp body
        return $ d{body = body'}
        
  resolveTExp e = error $ "Unknown iexp: " ++ show e

-- Adds "refs" at the end, effectively dereferencing Clafers when needed.
addRef :: PExp -> ErrorT ClaferSErr (ListT TypeAnalysis) PExp
addRef pexp =
  do
    localCurPath (typeOf pexp) $ do
      deref <- (ErrorT $ ListT $ resolveTPExp' $ newPExp $ IClaferId "" "ref" False) `catchError` const (lift mzero)
      let result = (newPExp $ IFunExp "." [pexp, deref]) `withType` typeOf deref
      return result <++> addRef result
  where
  newPExp = PExp Nothing "" $ inPos pexp
  
typeOf :: PExp -> IType
typeOf pexp = fromMaybe (error "No type") $ iType pexp

withType :: PExp -> IType -> PExp
withType p t = p{iType = Just t}

(<++>) :: (Error e, MonadPlus m) => ErrorT e m a -> ErrorT e m a -> ErrorT e m a
(ErrorT a) <++> (ErrorT b) = ErrorT $ a `mplus` b

liftError :: (MonadError e m, Error e) => ErrorT e m a -> ErrorT e m a
liftError e =
  liftCatch catchError e throwError
  where
  liftCatch catchError' m h = ErrorT $ runErrorT m `catchError'` (runErrorT . h)
