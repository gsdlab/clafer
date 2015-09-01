{-# LANGUAGE NamedFieldPuns, FlexibleInstances, FlexibleContexts, GeneralizedNewtypeDeriving #-}
{-
 Copyright (C) 2012-2015 Jimmy Liang, Kacper Bak, Michal Antkiewicz <http://gsd.uwaterloo.ca>

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
module Language.Clafer.Intermediate.ResolverType (resolveTModule)  where

import Language.ClaferT
import Language.Clafer.Common
import Language.Clafer.Intermediate.Intclafer hiding (uid)
import Language.Clafer.Intermediate.Desugarer
import Language.Clafer.Intermediate.TypeSystem
import Language.Clafer.Front.PrintClafer

import Control.Applicative
import Control.Exception (assert)
import Control.Lens ((&), (%~), traversed)
import Control.Monad.Except
import Control.Monad.List
import Control.Monad.Reader
import Data.Either
import Data.List
import Data.Maybe
import Prelude hiding (exp)

type TypeDecls = [(String, IType)]
data TypeInfo = TypeInfo {iTypeDecls::TypeDecls, iUIDIClaferMap::UIDIClaferMap, iCurThis::IClafer, iCurPath::Maybe IType}

newtype TypeAnalysis a = TypeAnalysis (ReaderT TypeInfo (Either ClaferSErr) a)
  deriving (MonadError ClaferSErr, Monad, Functor, MonadReader TypeInfo, Applicative)

-- return the type of a UID but give preference to local declarations in quantified expressions, which shadow global names
typeOfUid :: MonadTypeAnalysis m => UID -> m IType
typeOfUid uid = (fromMaybe (TClafer [uid]) . lookup uid) <$> typeDecls

class (Functor m, Monad m) => MonadTypeAnalysis m where
  -- What "this" refers to
  curThis :: m IClafer
  localCurThis :: IClafer -> m a -> m a

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

instance MonadTypeAnalysis m => MonadTypeAnalysis (ExceptT ClaferSErr m) where
  curThis = lift $ curThis
  localCurThis = mapExceptT . localCurThis
  curPath = lift $ curPath
  localCurPath = mapExceptT . localCurPath
  typeDecls = lift typeDecls
  localDecls = mapExceptT . localDecls

-- | Type inference and checking
runTypeAnalysis :: TypeAnalysis a -> IModule -> Either ClaferSErr a
runTypeAnalysis (TypeAnalysis tc) imodule = runReaderT tc $ TypeInfo [] (createUidIClaferMap imodule) undefined Nothing

claferWithUid :: (Monad m) => UIDIClaferMap -> String -> m IClafer
claferWithUid uidIClaferMap' u = case findIClafer uidIClaferMap' u of
  Just c -> return c
  Nothing -> fail $ "ResolverType.claferWithUid: " ++ u ++ " not found!"

parentOf :: (Monad m) => UIDIClaferMap -> UID -> m UID
parentOf uidIClaferMap' c = case _parentUID <$> findIClafer uidIClaferMap' c of
  Just u -> return u
  Nothing -> fail $ "ResolverType.parentOf: " ++ c ++ " not found!"

{-
 - C is an direct child of B.
 -
 -  abstract A
 -    C      // C - child
 -  B : A    // B - parent
 -}
isIndirectChild :: (Monad m) => UIDIClaferMap -> UID -> UID -> m Bool
isIndirectChild uidIClaferMap' child parent = do
  (_:allSupers) <- hierarchy uidIClaferMap' parent
  childOfSupers <- mapM ((isChild uidIClaferMap' child)._uid) $ allSupers
  return $ or childOfSupers

isChild :: (Monad m) => UIDIClaferMap -> UID -> UID -> m Bool
isChild uidIClaferMap' child parent =
    (case findIClafer uidIClaferMap' child of
            Nothing -> return False
            Just childIClafer -> do
                let directChild = (parent == _parentUID childIClafer)
                indirectChild <- isIndirectChild uidIClaferMap' child parent
                return $ directChild || indirectChild
            )

str :: IType -> String
str t =
  case unionType t of
    [t'] -> t'
    ts   -> "[" ++ intercalate "," ts ++ "]"

showType :: PExp                   -> String
showType    PExp{ _iType=Nothing }  = "unknown type"
showType    PExp{ _iType=(Just t) } = show t

data TAMode
  = TAReferences    -- | Phase one: only process references
  | TAExpressions   -- | Phase two: only process constraints and goals

resolveTModule :: (IModule, GEnv) -> Either ClaferSErr IModule
resolveTModule (imodule, _) =
  case runTypeAnalysis (analysisReferences $ _mDecls imodule) imodule of
    Right mDecls' -> case runTypeAnalysis (analysisExpressions $ mDecls') imodule{_mDecls = mDecls'} of
      Right mDecls'' -> return imodule{_mDecls = mDecls''}
      Left err      -> throwError err
    Left err      -> throwError err
  where
  analysisReferences = mapM (resolveTElement TAReferences rootIdent)
  analysisExpressions = mapM (resolveTElement TAExpressions rootIdent)

-- Phase one: only process references
resolveTElement :: TAMode     -> String -> IElement          -> TypeAnalysis IElement
resolveTElement    TAReferences  _         (IEClafer iclafer) =
  do
    uidIClaferMap' <- asks iUIDIClaferMap
    reference' <- case _reference iclafer of
      Nothing -> return Nothing
      Just originalReference -> do
        refs' <- resolveTPExp $ _ref originalReference
        case refs' of
          []     -> return Nothing
          [ref'] -> return $ refWithNewType uidIClaferMap' originalReference ref'
          (ref':_) -> return $ refWithNewType uidIClaferMap' originalReference ref'
    elements' <- mapM (resolveTElement TAReferences (_uid iclafer)) (_elements iclafer)
    return $ IEClafer iclafer{_elements = elements', _reference=reference'}
  where
    refWithNewType uMap oRef r = let
        r' = r & iType.traversed %~ (addHierarchy uMap)
      in case _iType r' of
        Nothing -> Nothing
        Just t -> if isTBoolean t
                  then Nothing
                  else Just $ oRef{_ref=r'}
resolveTElement    TAReferences  _         iec@(IEConstraint{}) = return iec
resolveTElement    TAReferences  _         ieg@(IEGoal{}) = return ieg

-- Phase two: only process constraints and goals
resolveTElement    TAExpressions  _         (IEClafer iclafer) =
  do
    elements' <- mapM (resolveTElement TAExpressions (_uid iclafer)) (_elements iclafer)
    return $ IEClafer iclafer{_elements = elements'}
resolveTElement    TAExpressions parent'   (IEConstraint _isHard _pexp) =
  IEConstraint _isHard <$> (testBoolean =<< resolveTConstraint parent' _pexp)
  where
  testBoolean pexp' =
    do
      unless (isTBoolean $ typeOf pexp') $
        throwError $ SemanticErr (_inPos pexp') ("Cannot construct constraint on type '" ++ showType pexp' ++ "'")
      return pexp'
resolveTElement    TAExpressions parent' (IEGoal isMaximize' pexp') =
  IEGoal isMaximize' <$> resolveTConstraint parent' pexp'

resolveTConstraint :: String -> PExp -> TypeAnalysis PExp
resolveTConstraint curThis' constraint =
  do
    uidIClaferMap' <- asks iUIDIClaferMap
    curThis'' <- claferWithUid uidIClaferMap' curThis'
    head <$> (localCurThis curThis'' $ (resolveTPExp constraint :: TypeAnalysis [PExp]))


resolveTPExp :: PExp -> TypeAnalysis [PExp]
resolveTPExp p =
  do
    x <- resolveTPExp' p
    case partitionEithers x of
      (f:_, []) -> throwError f                       -- Case 1: Only fails. Complain about the first one.
      ([], [])  -> throwError $ SemanticErr (_inPos p) ("No results but no errors for " ++ show p) -- Case 2: No success and no error message. Bug.
      (_,   xs) -> return xs                          -- Case 3: At least one success.

resolveTPExp' :: PExp -> TypeAnalysis [Either ClaferSErr PExp]
resolveTPExp' p@PExp{_inPos, _exp = IClaferId{_sident = "dref"}} = do
  uidIClaferMap' <- asks iUIDIClaferMap
  runListT $ runExceptT $ do
    curPath' <- curPath
    case curPath' of
      Just curPath'' -> do
        case concatMap (getTMaps uidIClaferMap') $ getTClafers uidIClaferMap' curPath'' of
          [t'] -> return $ p `withType` t'
          (t':_) -> return $ p `withType` t'
          [] -> throwError $ SemanticErr _inPos ("Cannot deref from type '" ++ str curPath'' ++ "'")
      Nothing -> throwError $ SemanticErr _inPos ("Cannot deref at the start of a path")
resolveTPExp' p@PExp{_inPos, _exp = IClaferId{_sident = "parent"}} = do
  uidIClaferMap' <- asks iUIDIClaferMap
  runListT $ runExceptT $ do
    curPath' <- curPath
    case curPath' of
      Just curPath'' -> do
        parent' <- fromUnionType <$> runListT (parentOf uidIClaferMap' =<< liftList (unionType curPath''))
        when (isNothing parent') $
          throwError $ SemanticErr _inPos "Cannot parent from root"
        let result = p `withType` fromJust parent'
        return result
      Nothing -> throwError $ SemanticErr _inPos "Cannot parent at the start of a path"
resolveTPExp' p@PExp{_exp = IClaferId{_sident = "integer"}} = runListT $ runExceptT $ return $ p `withType` TInteger
resolveTPExp' p@PExp{_exp = IClaferId{_sident = "int"}} = runListT $ runExceptT $ return $ p `withType` TInteger
resolveTPExp' p@PExp{_exp = IClaferId{_sident = "string"}} = runListT $ runExceptT $ return $ p `withType` TString
resolveTPExp' p@PExp{_exp = IClaferId{_sident = "double"}} = runListT $ runExceptT $ return $ p `withType` TDouble
resolveTPExp' p@PExp{_exp = IClaferId{_sident = "real"}} = runListT $ runExceptT $ return $ p `withType` TReal
resolveTPExp' p@PExp{_inPos, _exp = IClaferId{_sident="this"}} = do
  runListT $ runExceptT $ do
    sident' <- _uid <$> curThis
    result <- (p `withType`) <$> typeOfUid sident'
    return result
      <++>
      addDref result -- Case 2: Dereference the sident 1..* times
resolveTPExp' p@PExp{_inPos, _exp = IClaferId{_sident, _isTop}} = do
  uidIClaferMap' <- asks iUIDIClaferMap
  runListT $ runExceptT $ do
    curPath' <- curPath
    sident' <- if _sident == "this" then _uid <$> curThis else return _sident
    when (isJust curPath') $ do
      c <- mapM (isChild uidIClaferMap' sident') $ unionType $ fromJust curPath'
      unless (or c) $ throwError $ SemanticErr _inPos ("'" ++ sident' ++ "' is not a child of type '" ++ str (fromJust curPath') ++ "'")
    result <- (p `withType`) <$> typeOfUid sident'
    if _isTop
    then return result -- Case 1: Use the sident
          <++>
          addDref result -- Case 2: Dereference the sident 1..* times
          <++>
          addSome result
    else return result -- all not top-level identifiers must be in a path


resolveTPExp' p@PExp{_inPos, _exp} =
  runListT $ runExceptT $ (case _exp of
    e@IFunExp {_op = ".", _exps = [arg1, arg2]} -> do
        (iType', exp') <-  do
            arg1' <- lift $ ListT $ resolveTPExp arg1
            localCurPath (typeOf arg1') $ do
                arg2' <- liftError $ lift $ ListT $ resolveTPExp arg2
                (case _iType arg2' of
                    Just (t'@TClafer{}) -> return (t', e{_exps = [arg1', arg2']})
                    Just (TMap{_ta=t'}) -> return (t', e{_exps = [arg1', arg2']})
                    _ -> fail $ "Function '.' cannot be performed on " ++ showType arg1' ++ "\n.\n " ++ showType arg2')
        let result = p{_iType = Just iType', _exp = exp'}
        return result -- Case 1: Use the sident
          <++>
          addDref result -- Case 2: Dereference the sident 1..* times
          <++>
          addSome result
    _ -> do
      (iType', exp') <- ExceptT $ ListT $ resolveTExp _exp
      return p{_iType = Just iType', _exp = exp'})
  where
  resolveTExp :: IExp -> TypeAnalysis [Either ClaferSErr (IType, IExp)]
  resolveTExp e@(IInt _)    = runListT $ runExceptT $ return (TInteger, e)
  resolveTExp e@(IDouble _) = runListT $ runExceptT $ return (TDouble, e)
  resolveTExp e@(IReal _) = runListT $ runExceptT $ return (TReal, e)
  resolveTExp e@(IStr _)    = runListT $ runExceptT $ return (TString, e)

  resolveTExp e@IFunExp {_op, _exps = [arg]} =
    runListT $ runExceptT $ do
      arg' <- lift $ ListT $ resolveTPExp arg
      let t = typeOf arg'
      let
          test c =
            unless c $
              throwError $ SemanticErr _inPos ("Function '" ++ _op ++ "' cannot be performed on " ++ _op ++ " '" ++ showType arg' ++ "'")
      let result
            | _op == iNot = test (isTBoolean t) >> return TBoolean
            | _op == iCSet = return TInteger
            | _op == iSumSet = test (isTInteger t) >> return TInteger
            | _op == iProdSet = test (isTInteger t) >> return TInteger
            | _op `elem` [iMin, iGMin, iGMax] = test (numeric t) >> return t
            | otherwise = assert False $ error $ "Unknown op '" ++ _op ++ "'"
      result' <- result
      return (result', e{_exps = [arg']})

  resolveTExp e@IFunExp {_op = "++", _exps = [arg1, arg2]} =
    do
      arg1s' <- resolveTPExp arg1
      arg2s' <- resolveTPExp arg2
      let union' a b = typeOf a +++ typeOf b
      return $ [ return (union' arg1' arg2', e{_exps = [arg1', arg2']})
               | (arg1', arg2') <- sortBy (comparing $ length . unionType . uncurry union') $ liftM2 (,) arg1s' arg2s'
               , (not $ isTBoolean $ typeOf arg1') && (not $ isTBoolean $ typeOf arg2') ]
  resolveTExp e@IFunExp {_op, _exps = [arg1, arg2]} = do
    uidIClaferMap' <- asks iUIDIClaferMap
    runListT $ runExceptT $ do
      arg1' <- lift $ ListT $ resolveTPExp arg1
      arg2' <- lift $ ListT $ resolveTPExp arg2
      let t1 = typeOf arg1'
      let t2 = typeOf arg2'
      let testIntersect e1 e2 =
            do
              it <- intersection uidIClaferMap' e1 e2
              case it of
                Just it' -> if isTBoolean it'
                            then throwError $ SemanticErr _inPos ("Function '" ++ _op ++ "' cannot be performed on\n" ++ showType arg1' ++ "\n" ++ _op ++ "\n" ++ showType arg2')
                            else return it'
                Nothing  -> throwError $ SemanticErr _inPos ("Function '" ++ _op ++ "' cannot be performed on\n" ++ showType arg1' ++ "\n" ++ _op ++ "\n" ++ showType arg2')
      let testNotSame e1 e2 =
            when (e1 `sameAs` e2) $
              throwError $ SemanticErr _inPos ("Function '" ++ _op ++ "' is redundant because the two subexpressions are always equivalent")
      let test c =
            unless c $
              throwError $ SemanticErr _inPos ("Function '" ++ _op ++ "' cannot be performed on\n" ++ showType arg1' ++ "\n" ++ _op ++ "\n" ++ showType arg2')
      let result
            | _op `elem` logBinOps = test (isTBoolean t1 && isTBoolean t2) >> return TBoolean
            | _op `elem` [iLt, iGt, iLte, iGte] = test (numeric t1 && numeric t2) >> return TBoolean
            | _op `elem` [iEq, iNeq] = testNotSame arg1' arg2' >> testIntersect t1 t2 >> return TBoolean
            | _op == iDifference = testNotSame arg1' arg2' >> testIntersect t1 t2 >> return t1
            | _op == iIntersection = testNotSame arg1' arg2' >> testIntersect t1 t2
            | _op `elem` [iDomain, iRange] = testIntersect t1 t2
            | _op `elem` relSetBinOps = testIntersect t1 t2 >> return TBoolean
            | _op `elem` [iSub, iMul, iDiv, iRem] = test (numeric t1 && numeric t2) >> return (coerce t1 t2)
            | _op == iPlus =
                (test (isTString t1 && isTString t2) >> return TString) -- Case 1: String concatenation
                `catchError`
                const (test (numeric t1 && numeric t2) >> return (coerce t1 t2)) -- Case 2: Addition
            | otherwise = error $ "ResolverType: Unknown op: " ++ show e
      result' <- result
      return (result', e{_exps = [arg1', arg2']})

  resolveTExp e@(IFunExp "ifthenelse" [arg1, arg2, arg3]) = do
    uidIClaferMap' <- asks iUIDIClaferMap
    runListT $ runExceptT $ do
      arg1' <- lift $ ListT $ resolveTPExp arg1
      arg2' <- lift $ ListT $ resolveTPExp arg2
      arg3' <- lift $ ListT $ resolveTPExp arg3
      let t1 = typeOf arg1'
      let t2 = typeOf arg2'
      let t3 = typeOf arg3'

      unless (isTBoolean t1) $
        throwError $ SemanticErr _inPos ("The type of condition in 'if/then/else' must be 'TBoolean', insted it is " ++ showType arg1')

      it <- getIfThenElseType uidIClaferMap' t2 t3
      t <- case it of
        Just it' -> return it'
        Nothing  -> throwError $ SemanticErr _inPos ("Function 'if/then/else' cannot be performed on \nif\n" ++ showType arg1' ++ "\nthen\n" ++ showType arg2' ++ "\nelse\n" ++ showType arg3')

      return (t, e{_exps = [arg1', arg2', arg3']})
  -- some P, no P, one P
  -- P must not be TBoolean
  resolveTExp e@IDeclPExp{_oDecls=[], _bpexp} =
    runListT $ runExceptT $ do
      bpexp' <- liftError $ lift $ ListT $ resolveTPExp _bpexp
      case _iType bpexp' of
          Nothing -> fail $ "resolveTExp@IDeclPExp: No type computed for body\n" ++ show bpexp'
          Just t' -> if  isTBoolean t'
                     then throwError $ SemanticErr _inPos "The type of body of a quantified expression without local declarations must not be 'TBoolean'"
                     else return $ (TBoolean, e{_bpexp = bpexp'})
  -- some x : X | P, no x : X | P, one x : X | P
  -- X must not be TBoolean, P must be TBoolean
  resolveTExp e@IDeclPExp{_oDecls, _bpexp} =
    runListT $ runExceptT $ do
      oDecls' <- mapM resolveTDecl _oDecls
      let extraDecls = [(decl, typeOf $ _body oDecl) | oDecl <- oDecls', decl <- _decls oDecl]
      localDecls extraDecls $ do
        bpexp' <- liftError $ lift $ ListT $ resolveTPExp _bpexp
        case _iType bpexp' of
            Nothing -> fail $ "resolveTExp@IDeclPExp: No type computed for body\n" ++ show bpexp'
            Just t' -> if  isTBoolean t'
                       then return $ (TBoolean, e{_oDecls = oDecls', _bpexp = bpexp'})
                       else throwError $ SemanticErr _inPos $ "The type of body of a quantified expression with local declarations must be 'TBoolean', instead it is\n" ++ showType bpexp'
    where
    resolveTDecl d@IDecl{_body} =
      do
        body' <- lift $ ListT $ resolveTPExp _body
        case _iType body' of
            Nothing -> fail $ "resolveTExp@IDeclPExp: No type computed for local declaration\n" ++ show body'
            Just t' -> if  isTBoolean t'
                       then throwError $ SemanticErr _inPos "The type of declaration of a quantified expression must not be 'TBoolean'"
                       else return $ d{_body = body'}
  resolveTExp e = error $ "Unknown iexp: " ++ show e

-- Adds "dref"s at the end, effectively dereferencing Clafers when needed.
addDref :: PExp -> ExceptT ClaferSErr (ListT TypeAnalysis) PExp
addDref pexp =
  do
    localCurPath (typeOf pexp) $ do
      deref <- (ExceptT $ ListT $ resolveTPExp' $ newPExp $ IClaferId "" "dref" False Nothing) `catchError` const (lift mzero)
      let result = (newPExp $ IFunExp "." [pexp, deref]) `withType` typeOf deref
      return result <++> addDref result
  where
  newPExp = PExp Nothing "" $ _inPos pexp

-- Adds a quantifier "some" at the beginning, effectively turning an identifier into a TBoolean expression
addSome :: PExp -> ExceptT ClaferSErr (ListT TypeAnalysis) PExp
addSome pexp =
  do
    localCurPath (typeOf pexp) $ return $ (newPExp $ IDeclPExp ISome [] pexp) `withType` TBoolean
  where
  newPExp = PExp Nothing "" $ _inPos pexp

typeOf :: PExp -> IType
typeOf pexp = fromMaybe (error "No type") $ _iType pexp

withType :: PExp -> IType -> PExp
withType p t = p{_iType = Just t}

(<++>) :: MonadPlus m => ExceptT e m a -> ExceptT e m a -> ExceptT e m a
(ExceptT a) <++> (ExceptT b) = ExceptT $ a `mplus` b

liftError :: MonadError e m => ExceptT e m a -> ExceptT e m a
liftError e =
  liftCatch catchError e throwError
  where
  liftCatch catchError' m h = ExceptT $ runExceptT m `catchError'` (runExceptT . h)

{-
 -
 - Utility functions
 -
 -}

liftList :: Monad m => [a] -> ListT m a
liftList = ListT . return

comparing :: Ord b => (a -> b) -> a -> a -> Ordering
comparing f a b = f a `compare` f b

syntaxOf :: PExp -> String
syntaxOf = printTree . sugarExp

-- Returns true iff the left and right expressions are syntactically identical
sameAs :: PExp -> PExp -> Bool
sameAs e1 e2 = syntaxOf e1 == syntaxOf e2 -- Not very efficient but hopefully correct
