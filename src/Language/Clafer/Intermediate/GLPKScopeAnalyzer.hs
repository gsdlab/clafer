{-# LANGUAGE GeneralizedNewtypeDeriving, UndecidableInstances, FlexibleInstances, FlexibleContexts, MultiParamTypeClasses, NamedFieldPuns, TupleSections #-}

{-
 Copyright (C) 2012-2013 Jimmy Liang, Kacper Bak <http://gsd.uwaterloo.ca>

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
module Language.Clafer.Intermediate.GLPKScopeAnalyzer (glpkScopeAnalysis) where

import Language.Clafer.Front.Absclafer hiding (Path)
import qualified Language.Clafer.Intermediate.Intclafer as I
import Language.Clafer.Intermediate.Analysis
import Language.Clafer.Intermediate.ResolverType

import Control.Applicative (Applicative(..), (<$>))
import Control.Monad
import Control.Monad.List
import Control.Monad.LPMonad
import Control.Monad.Maybe
import Control.Monad.Reader
import Control.Monad.State
import Data.Either
import Data.LinearProgram hiding (constraints)
import Data.List
import Data.Map ()
import qualified Data.Map as Map
import Data.Maybe
import System.IO.Unsafe
import Text.Parsec.Combinator
import Text.Parsec.Error
import Text.Parsec.Pos
import Text.Parsec.Prim
import Text.Parsec.String ()


{------------------------------------------------------------
 ---------- Linear programming ------------------------------
 ------------------------------------------------------------}

-- | Compute scopes for clafers by solving a system of linear equations
glpkScopeAnalysis :: I.IModule -> [(String, Integer)]
glpkScopeAnalysis imodule =
  intScope ++ scopes
  where
  intScope = if bitwidth > 4 then return ("int", bitwidth) else fail "Bitwidth less than default."
  bitwidth = bitwidthAnalysis (constants ++ map snd scopes)
  
  scopes = 
      removeZeroes $ removeRoot $ removeAux $
      -- unsafePerformIO should be safe (?)
      -- We aren't modifying any global state.
      -- If we don't use unsafePerformIO, then we have to be inside the IO monad and
      -- makes things really ugly. Might as well contain the ugliness in here.
      case unsafePerformIO solution of
        (Success, Just (_, s)) -> Map.toList $ Map.map round s
        _ -> [] -- No solution
  
  ((_, constants), analysis) = runScopeAnalysis run $ gatherInfo imodule
  
  run =
    do
      setConstraints
      abstracts' <- clafers `suchThat` isAbstract
      constants' <- constantsAnalysis
      return (abstracts', constants')
  
  solution = {-trace (show $ unsafePerformIO $ writeLP "TESTTT" analysis) $-} glpSolveVars mipDefaults{msgLev = MsgOff} $ analysis
  -- Any scope that is 0 will take the global scope of 1 instead.
  removeZeroes = filter ((/= 0) . snd)
  -- The root is implied and not and not part of the actual solution.
  removeRoot = filter ((/= rootUid) . fst)
  -- Auxilary variables are only part of the computation, not the solution.
  removeAux = filter (not . (uniqNameSpace `isPrefixOf`) . fst)
  -- The scope for abstract clafers are removed. Alloy doesn't need it. Makes
  -- it easier use since user can increase the scope of subclafers without
  -- needing to increase the scope of the abstract Clafer.
  --removeAbstracts = filter (not . (`elem` map uid abstracts) . fst)


bitwidthAnalysis :: [Integer] -> Integer
bitwidthAnalysis constants =
  toInteger $ 1 + fromJust (findIndex (\x -> all (`within` x) constants) bitRange)
  where
  within a (minB, maxB) = a >= minB && a <= maxB
  bitRange = [(-2^i, 2^i-1) | i <- ([0..]::[Integer])]

  
-- Returns all constant literals
constantsAnalysis :: ScopeAnalysis [Integer]
constantsAnalysis =
  do
    cons <- constraintsUnder anything `select` snd
    return $ mapMaybe integerConstant [I._exp sub | con <- cons, sub <- subexpressions con]
  where  
  integerConstant (I.IInt i) = Just i
  integerConstant _ = Nothing
  

-- (-1) for infinity
data Between =
    Between Integer Integer
    deriving Show

--atLeastOne :: Between -> Bool
--atLeastOne (Between i _) = i >= 1
{-
overlap :: Between -> Between -> Maybe Between
overlap (Between l1 h1) (Between l2 h2)
    | l1 > h2 && h2 /= -1 = Nothing
    | l2 > h1 && h1 /= -1 = Nothing
    | otherwise = Just $ Between (maxx l1 l2) (minn h1 h2)
    where
    minn (-1) b = b
    minn a (-1) = a
    minn a b = min a b
    
    maxx (-1) _ = -1
    maxx _ (-1) = -1
    maxx a b = max a b

overlapM :: Maybe Between -> Maybe Between -> Maybe Between
overlapM a b =
    do
        a' <- a
        b' <- b
        overlap a' b'
-} 
    
-- Multiplies two positive integers where -1=infinity
mult :: Integer -> Integer -> Integer
mult (-1) _ = -1
mult _ (-1) = -1
mult a b = a * b



simpleAnalysis :: ScopeAnalysis [(String, Between)]
simpleAnalysis =
    do
        root <- claferWithUid rootUid
        analysis <- simpleAnalysis' root (Between 1 1)
        --moreAnalysis <- simpleConstraintAnalysis analysis
        return analysis
    where
    simpleAnalysis' cur cb@(Between l h) =
        runListT $ return (uid cur, cb) `mplus` do
            child <- foreach $ (anything |^ cur) `select` fst
            let b
                 | groupLow cur == 0 && groupHigh cur == -1 = Between (low child * l) (high child `mult` h)
                 | otherwise                                = Between 0 (-1)
            foreach (simpleAnalysis' child b)
{-    
    mergeAnalysis analysis =
        [(n, fromJust x) | (n, b) <- combine analysis, let x = foldr1 overlapM $ map Just b, isJust x]
  
    simpleConstraintAnalysis :: [(String, Between)] -> ScopeAnalysis [(String, Between)]
    simpleConstraintAnalysis analysis = mergeAnalysis <$> simpleConstraintAnalysis' analysis
    
    simpleConstraintAnalysis' analysis =
        runListT $ do
            (curThis, cons) <- foreach $ constraintsUnder anything
            constraintBetween curThis (I._exp cons)
        where
        constraintBetween _ I.IDeclPExp {I._quant = I.ISome, I._oDecls = [], I._bpexp} =
            do
                let t = map tLexeme $ fromMaybe [] $ unfoldJoins bpexp
                guard (not $ null t)
                guard ("this" `notElem` t)
                guard ("parent" `notElem` t)
                guard ("ref" `notElem` t)
                msum $ map someStep t
        constraintBetween curThis I.IFunExp{I._op = "&&", I._exps = [exp1, exp2]} =
            constraintBetween curThis (I._exp exp1) `mplus` constraintBetween curThis (I._exp exp2)
        constraintBetween _ _ = mzero
        someStep step =
            do
                parent <- parentOf step
                let parentBetween = fromMaybe (error $ "Missing parent " ++ parent) $ lookup parent analysis
                guard $ atLeastOne parentBetween
                return (step, Between 1 $ -1)
-}       
    

setConstraints :: ScopeAnalysis ()
setConstraints =
  do
    simpleAnalysis
    p <- flatten
    withExtraClafers p $ do
        optFormula
        colonConstraints
        refConstraints
        parentConstraints
        constraintConstraints

    (var rootUid) `equalTo` 1


optFormula :: ScopeAnalysis ()
optFormula =
  do
    setDirection Min
    c <- clafers
    let concretes = [uid concrete | concrete <- c, isConcrete concrete, isDerived concrete, not $ uniqNameSpace `isPrefixOf` uid concrete]
    setObjective $ varSum concretes

parentConstraints :: ScopeAnalysis ()
parentConstraints =
  runListT_ $ do
    -- forall child under parent ...
    (child, parent) <- foreach $ anything |^ anything

    let uchild = uid child
    let uparent = uid parent
    
    if low child == high child
        -- Saves us one constraint
        then do
            var uchild `equal` (low child *^ var uparent)
        else do
            -- ... scope_this <= scope_parent * low-card(this) ...
            var uchild `geq` (low child *^ var uparent)
            -- ... scope_this >= scope_parent * high-card(this) ...
            -- high == -1 implies high card is unbounded

            if high child /= -1
              then var uchild `leq` (high child *^ var uparent)
              {-
               - A
               -   B *
               - [#B = 4]
               -
               - Need this constraint so that #A=1
               -}
              else (smallM *^ var uchild) `leq` var uparent
            -- Use integer's not doubles
            setVarKind uchild IntVar
            setVarKind uparent IntVar


refConstraints :: ScopeAnalysis ()
refConstraints =
  runListT_ $ do
    -- for all uids of any clafer the refs another uid ...
    (sub, sup) <- foreach $ (anything |-> anything) `suchThat` (isDerived . superClafers)
    let usub = uid sub
    let usup = uid sup
    aux <- testPositive usub
    -- scope_sup >= low-card(sub)
    var usup `geq` ((max 1 $ low sub) *^ var aux)


colonConstraints :: ScopeAnalysis ()
colonConstraints =
  runListT_ $ do
    -- forall c in the set of clafers' uid ...
    c <- foreach $ clafers `suchThat` isDerived
    -- ... find all uids of any clafer that extends c (only colons) ...
    subs <- findAll $ (anything |: c) `select` (uid . subClafers)
    when (not $ null subs) $
      -- ... then set the constraint scope_C = sum scope_subs
      var (uid c) `equal` varSum subs



flatten :: ScopeAnalysis [SClafer]        
flatten =
    runListT $ do
        abs' <- clafers `suchThat` isAbstract
        (c, s) <- foreach $ anything |: anything
        ListT $ runReaderT (addChildren (map uid abs') (Part [uid c, uid s]) (Part [])) []
        
addChildren :: MonadAnalysis m => [String] -> Part -> Part -> m [SClafer]        
addChildren abs' (Part steps) ss@(Part supSteps) =
    do
        let parBase = last steps
        
        chis <- directChildrenOf parBase
        achis <- forM chis $
            \chi -> do
                let chiP = Part $ init steps ++ [chi]
                let par  = Part steps
                let supP = Part $ supSteps ++ [chi]
                
                chiC <- claferWithUid chi
                let s = SClafer (reifyPartName chiP) chi False (low chiC) (high chiC) (groupLow chiC) (groupHigh chiC) (Just $ reifyPartName par) (Just $ Colon $ reifyPartName supP) (constraints chiC)
                return s <:> addChildren abs' chiP ss
        
        col <- runMaybeT $ colonOf parBase
        case col of
            Just col' -> do
                acol <- addChildren abs' (Part $ steps ++ [col']) (Part $ supSteps ++ [parBase])
                return $ concat achis ++ acol
            Nothing -> return $ concat achis
    where
    notAbs = not . (`elem` abs')
    reifyPartName (Part (t : target)) = reifyPartName' $ t : filter notAbs target
    reifyPartName (Part []) = error "Function reifyPartName from GLPKScopeAnalyzer expects a non empty Part, but was given one!" -- This should never happen
    reifyPartName' [target] = target
    reifyPartName' target   = uniqNameSpace ++ "reify_" ++ intercalate "_" target        


data Path =
  Path {parts::[Part]}
  deriving (Eq, Ord, Show)

data Part =
  Part {steps::[String]}
  deriving (Eq, Ord, Show)


{-data Expr =
    This {path::Path, eType::I.IType} |
    Global {path::Path, eType::I.IType} |
    Const Integer |
    Concat {paths::[Expr], eType::I.IType} |
    Positive {allPaths :: [Path], num::Integer, eType::I.IType}
    deriving Show-}

data Expr =
    This Path I.IType |
    Global Path I.IType |
    Const Integer |
    Concat [Expr] I.IType |
    Positive [Path] Integer I.IType
    deriving Show

eType :: Expr -> I.IType
eType (This _ e) = e
eType (Global _ e) = e
eType (Concat _ e) = e
eType (Positive _ _ e) = e
eType (Const _) = error "Function eType from GLPK did not expect a Const"

isThis :: Expr -> Bool
isThis This{} = True
isThis _ = False
isGlobal :: Expr -> Bool
isGlobal Global{} = True
isGlobal _ = False
{-isConst :: Expr -> Bool
isConst Const{} = True
isConst _ = False-}
    
parentOfPart :: MonadAnalysis m => Part -> m Part
parentOfPart (Part s) =
  do
    s' <- parentOf $ last s
    cs' <- claferWithUid s'
    return $ if isAbstract cs'
      then Part $ init s
      else Part $ init s ++ [s']


{-
 - Turns constraints that look like:
 -
 -  [ A in List
 -    B in List ]
 - 
 - to
 -
 -  [ A, B in List ]
 -}
optimizeInConstraints :: [I.PExp] -> [I.PExp]
optimizeInConstraints constraints =
    noOpt ++ opt
    where
    (noOpt, toOpt) = partitionEithers (constraints >>= partitionConstraint)
    opt = [ unionPExpAll (map fst inSame) `inPExp` snd (head inSame)
            | inSame <- groupBy (testing' $ syntaxOf . snd) $ sortBy (comparing' snd) toOpt ]
    inPExp a b = I.PExp (Just I.TBoolean) "" noSpan $ I.IFunExp "in" [a, b]
    unionPExpAll es = foldr1 unionPExp es
    unionPExp a b = I.PExp (liftM2 (+++) (I._iType a) (I._iType b)) "" noSpan $ I.IFunExp "++" [a, b]
    
    partitionConstraint I.PExp{I._exp = I.IFunExp {I._op = "in", I._exps = [exp1, exp2]}} = return $ Right (exp1, exp2)
    partitionConstraint I.PExp{I._exp = I.IFunExp {I._op = "&&", I._exps = [exp1, exp2]}} = partitionConstraint exp1 `mplus` partitionConstraint exp2
    partitionConstraint e = return $ Left e

    testing'   f a b = f a == f b    
    comparing' f a b = f a `compare` f b


{-
 -   Phone *
 -
 -   [all p : Phone | <constraint on p>]
 -
 - becomes
 -
 -   Phone *
 -      [<constraint on p/this>]
 -}
optimizeAllConstraints :: MonadAnalysis m => SClafer -> [I.PExp] -> m [(SClafer, I.PExp)]
optimizeAllConstraints curThis constraints =
    runListT $ partitionConstraint =<< foreachM constraints
    where
    partitionConstraint I.PExp{I._exp = I.IDeclPExp I.IAll [I.IDecl _ [decl] I.PExp{I._exp = I.IClaferId{I._sident}}] bpexp} =
        do
            under <- claferWithUid _sident
            return (under, rename decl bpexp)
    partitionConstraint I.PExp{I._exp = I.IFunExp {I._op = "&&", I._exps = [exp1, exp2]}} = partitionConstraint exp1 `mplus` partitionConstraint exp2
    partitionConstraint e = return (curThis, e)
    
    rename :: String -> I.PExp -> I.PExp
    rename f p@I.PExp{I._exp = exp'} =
        p{I._exp = renameIExp exp'}
        where
        renameIExp (I.IFunExp op exps) = I.IFunExp op $ map (rename f) exps
        renameIExp (I.IDeclPExp quant oDecls bpexp) = I.IDeclPExp quant (map renameDecl oDecls) $ rename f bpexp
        renameIExp (I.IClaferId modName sident isTop bind)
            | f == sident = I.IClaferId modName "this" isTop bind
            | otherwise   = I.IClaferId modName sident isTop bind
        renameIExp i = i
        renameDecl (I.IDecl isDisj decls body)
            | f `elem` decls = I.IDecl isDisj decls body -- Not a free variable
            | otherwise      = I.IDecl isDisj decls $ rename f body -- Is a free variable

optConstraintsUnder :: MonadAnalysis m => SClafer -> m [(SClafer, [I.PExp])]
optConstraintsUnder clafer =
    do
        cons <- constraintsUnder clafer `select` snd
        allCons <- optimizeAllConstraints clafer cons
        let inCons = [(fst $ head c, optimizeInConstraints $ map snd c) | c <- groupBy (testing' $ uid . fst) $ sortBy (comparing' $ uid . fst) allCons]
        return inCons
    where
    testing' f a b = f a == f b
    comparing' f a b = f a `compare` f b


constraintConstraints :: MonadScope m => m ()
constraintConstraints =
  do
    runListT_ $ do
      clafer <- foreach clafers
      (supThis, cons) <- foreach $ optConstraintsUnder clafer
      
      con <- foreachM cons
      curThis <-
          if isAbstract supThis
              then
                  foreach $ colonsTo supThis
              else
                  return supThis
      constraint <- foreach $ scopeConstraint curThis con

      oneConstraint curThis constraint
  where
  --base (Part steps) = last steps
  
  oneConstraint c (e1, con, e2) =
    void $ runMaybeT $ oneConstraintOneWay c e1 con e2 `mplus` oneConstraintOneWay c e2 (reverseCon con) e1
  
  oneConstraintOneWay c@SClafer{uid} e1 con e2 =
    oneConstraint' e1 e2
    where
    oneConstraint' _ (This (Path []) _) =
      mzero
    oneConstraint' _ (Global (Path []) _) =
      mzero
    oneConstraint' (This (Path []) _) (This (Path parts) _) =
      return (var uid) `comp` reifyVar (last parts)
    oneConstraint' (This (Path []) _) (Global (Path parts) _) =
      return (var uid) `comp` reifyVar (last parts)
    oneConstraint' (Positive [Path []] _ _) _ =
      mzero
    oneConstraint' _ (Positive [Path []] _ _) =
      mzero
    oneConstraint' (Global (Path gParts) _) (Positive allPaths claf _) =
      do
        aux <- testPositives (map (reifyVarName . last . parts) allPaths)
        reifyVar (last gParts) `comp` return (claf *^ var aux)
    oneConstraint' (This (Path parts) _) (Const constant)
      | con == EQU            = oneConstraintOneWay c e1 LEQ e2 >> oneConstraintOneWay c e1 GEQ e2
      | con `elem` [GTH, GEQ] = foldM_ mkCon 1 (reverse parts)
      | con `elem` [LTH, LEQ] = reifyVar (last parts) `comp` (return $ (fromInteger constant :: Double) *^ var uid)
      where
      mkCon :: MonadScope m => Integer -> Part -> m Integer
      mkCon multiplier part =
        do
          let frac = (1 / fromInteger multiplier) * fromInteger constant :: Double
          (reifyVar part) `comp` return (frac *^ var uid)
          mult multiplier <$> prod part
    oneConstraint' (Global (Path parts) _) (Const constant)
      | con == EQU            = oneConstraintOneWay c e1 LEQ e2 >> oneConstraintOneWay c e1 GEQ e2
      | con `elem` [GTH, GEQ] =
          do
            k <- testPositive uid
            foldM_ (mkCon k) 1 (reverse parts)
      | con `elem` [LTH, LEQ] = reifyVar (last parts) `compTo` (return $ fromInteger constant)
      where
      mkCon :: MonadScope m => String -> Integer -> Part -> m Integer
      mkCon pos (-1) part =
        do
          (reifyVar part) `comp` return (var pos)
          return (-1)
      mkCon pos multiplier part =
        do
          let frac = (1 / fromInteger multiplier) * fromInteger constant :: Double
          (reifyVar part) `comp` return (frac *^ var pos)
          mult multiplier <$> prod part
        
    oneConstraint' (This (Path parts1) _) (This (Path parts2) _) =
      reifyVar (last parts1) `comp` reifyVar (last parts2)
    oneConstraint' (Global (Path parts1) _) (Global (Path parts2) _) =
      reifyVar (last parts1) `comp` reifyVar (last parts2)
    oneConstraint' (Global (Path parts) _) (Concat exprs _) =
      if all isGlobal exprs
        then reifyVar (last parts) `comp` reifyVars [last p | Global (Path p) _ <- exprs]
        else mzero
    oneConstraint' (This (Path parts) _) (Concat exprs _) =
      if all isGlobal exprs
        then do
          let vs = [last p | Global (Path p) _ <- exprs]
          claf <- mapM (claferWithUid . last . steps) $ vs
          s <- mapM constantCard claf
          p <- parentOfPart $ last parts
          reifyVar (last parts) `comp` ((sum s *^) <$> reifyVar p)
        else if all isThis exprs
          then reifyVar (last parts) `comp` reifyVars [last p | This (Path p) _ <- exprs]
          else mzero
    oneConstraint' _ _ = mzero
    
    constantCard SClafer{low, high}
      | low == high = return low
      | otherwise   = mzero
    
    prod (Part steps) = foldr1 mult <$> mapM (return . high <=< claferWithUid) steps
    
    comp x y =
      do
        x' <- x
        y' <- y
        case con of
          LTH -> (x' ^-^ y') `leqTo` (-smallM)
          LEQ -> x' `leq` y'
          EQU -> x' `equal` y'
          GTH -> (x' ^-^ y') `geqTo` smallM
          GEQ -> x' `geq` y'
    compTo x y =
      do
        x' <- x
        y' <- y
        case con of
          LTH -> x' `leqTo` (y' - smallM)
          LEQ -> x' `leqTo` y'
          EQU -> x' `equalTo` y'
          GTH -> x' `geqTo` (y' + smallM)
          GEQ -> x' `geqTo` y'

  reifyVar p  = return (var $ reifyVarName p)
  reifyVars p = return (varSum $ map reifyVarName p)
  reifyVarName (Part [target]) = target
  reifyVarName (Part target)   = uniqNameSpace ++ "reify_" ++ intercalate "_" target
{- 
  isAbstractPart (Part [_]) = False
  isAbstractPart _ = True

  reifiedSuper (Part steps) =
    do
      let (b : s : rest) = reverse steps
      ss <- colonOf s
      sss <- runMaybeT $ colonUid ss
      if isNothing sss
        then return $ Part $ reverse $ b : rest
        else return $ Part $ reverse $ b : ss : rest
  
  -- TODO: correct?

  siblingParts (Part (conc : abst)) =
    do
      conc' <- claferWithUid conc
      sup   <- runMaybeT $ colonOf conc'
      case sup of
        Nothing -> return [Part $ conc : abst]
        Just sup' -> runListT $ do
            (sub, _) <- foreach $ anything |: sup'
            return $ Part $ uid sub : abst
  siblingParts [] = error "Function siblingParts from GLpkScopeAnalyzer expects a non empty list, given an empty one!" -- This should never happen
  
  reifyPart (Part steps) =
    do
      as <- claferWithUid (last steps) >>= nonTopAncestors
      forM as $
        \a -> return $ Part $ init steps ++ [uid a]
  
  nonTopAncestors child =
    do
      parent <- parentOf child
      if uid parent == rootUid
        then return []
        else (++ [child]) `fmap` nonTopAncestors parent
 -} 

data Con = EQU | LTH | LEQ | GTH | GEQ deriving (Eq, Ord, Show)

reverseCon :: Con -> Con
reverseCon EQU = EQU
reverseCon LTH = GTH
reverseCon LEQ = GEQ
reverseCon GTH = LTH
reverseCon GEQ = LEQ
data Limit = Exact {lExpr::Expr} | AtLeast {lExpr::Expr} deriving Show

scopeConstraint :: MonadScope m => SClafer -> I.PExp -> m [(Expr, Con, Expr)]
scopeConstraint curThis pexp =
  runListT $ scopeConstraint' $ I._exp pexp
  where
  scopeConstraint' I.IFunExp {I._op = "&&", I._exps} = msum $ map (scopeConstraint' . I._exp) _exps
  scopeConstraint' I.IDeclPExp {I._quant = I.ISome, I._oDecls = [], I._bpexp} = parsePath curThis _bpexp `greaterThanEqual` constant (1::Integer)
  scopeConstraint' I.IDeclPExp {I._quant = I.ISome, I._oDecls}               = msum $ map pathAndMultDecl _oDecls
      where
      pathAndMultDecl I.IDecl {I._isDisj = True, I._decls, I._body} = parsePath curThis _body `greaterThanEqual` constant (length _decls)
      pathAndMultDecl I.IDecl {I._isDisj = False, I._body}         = parsePath curThis _body `greaterThanEqual` constant (1::Integer)
  scopeConstraint' I.IDeclPExp {I._quant = I.IOne, I._oDecls = [], I._bpexp} = parsePath curThis _bpexp `eqTo` constant (1::Integer)
  scopeConstraint' I.IDeclPExp {I._quant = I.IOne, I._oDecls} =
    do
      oDecl <- foreachM _oDecls
      parsePath curThis (I._body oDecl) `eqTo` constant (1::Integer)
  scopeConstraint' I.IFunExp {I._op, I._exps = [exp1, exp2]}
    | _op == "in" = inConstraint1 exp1 exp2 `mplus` inConstraint2 exp1 exp2
    | _op == "="  = equalConstraint1 exp1 exp2 `mplus` equalConstraint2 exp1 exp2
    | _op == "<"  = scopeConstraintNum exp1 `lessThan` scopeConstraintNum exp2
    | _op == "<=" = scopeConstraintNum exp1 `lessThanEqual` scopeConstraintNum exp2
    | _op == ">"  = scopeConstraintNum exp1 `greaterThan` scopeConstraintNum exp2
    | _op == ">=" = scopeConstraintNum exp1 `greaterThanEqual` scopeConstraintNum exp2
    | _op == "<=>" = (exp1 `implies` exp2) `mplus` (exp2 `implies` exp1)
    | _op == "=>" = exp1 `implies` exp2
  scopeConstraint' _ = mzero
  
  implies exp1 exp2 =
    do
      e1 <- scopeConstraint' $ I._exp exp1
      e2 <- scopeConstraint' $ I._exp exp2

      case (e1, e2) of
        ((This thisPath t1, GEQ, Const 1), (Global globalPath t0, comp, Positive allPaths c t2)) ->
          return $ (Global globalPath t0, comp, Positive (thisPath : allPaths) c $ t1 +++ t2)
        ((This thisPath e1', GEQ, Const 1), (Global globalPath e2', comp, Const c)) ->
          return $ (Global globalPath e2', comp, Positive [thisPath] c e1')
        ((Global path1 t1, GEQ, Const 1), (Global path2 t0, comp, Positive allPaths c t2)) ->
          return $ (Global path2 t0, comp, Positive (path1 : allPaths) c $ t1 +++ t2)
        ((Global path1 e1', GEQ, Const 1), (Global path2 e2', comp, Const c)) ->
          return $ (Global path2 e2', comp, Positive [path1] c e1')
        ((t1@(This (Path [thisPart1]) _), GEQ, Const 1), (t2@(This (Path [_]) _), GEQ, Const 1)) ->
            do
                c <- claferWithUid $ last $ steps thisPart1
                guard (high c == 1)
                return (t2, GEQ, t1)
        _ -> mzero

  equalConstraint1 exp1 exp2 =
    do
      l1 <- scopeConstraintSet exp1
      l2 <- scopeConstraintSet exp2
      case (l1, l2) of
        (Exact e1, Exact e2)   -> return e1 `eqTo` return e2
        (AtLeast e1, Exact e2) -> return e1 `greaterThanEqual` return e2
        (Exact e1, AtLeast e2) -> return e1 `lessThanEqual` return e2
        _ -> mzero
  equalConstraint2 exp1 exp2 = scopeConstraintNum exp1 `eqTo` scopeConstraintNum exp2
  
  -- exp1 in exp2
  inConstraint1 exp1 exp2 =
    do
      l1 <- scopeConstraintSet exp1
      l2 <- scopeConstraintSet exp2

      case l2 of
        Exact e2 -> return (lExpr l1) `lessThanEqual` return e2
        _ -> mzero
  inConstraint2 exp1 exp2 = scopeConstraintNum exp1 `lessThanEqual` scopeConstraintNum exp2

  scopeConstraintSet I.PExp {I._exp = I.IFunExp {I._op = "++", I._exps = [e1, e2]}} =
    do
      l1' <- scopeConstraintSet e1
      l2' <- scopeConstraintSet e2
      i   <- intersects (eType $ lExpr l1') (eType $ lExpr l2')
      if i
        then return $ AtLeast $ lExpr l1'
        else return $ combineDisjoint l1' l2'
  scopeConstraintSet x = Exact <$> parsePath curThis x
  
  combineDisjoint (Exact e1) (Exact e2) =
    Exact (Concat ([e1, e2] >>= flattenConcat) $ eType e1 +++ eType e2)
  combineDisjoint l1 l2 =
    AtLeast (Concat ([e1, e2] >>= flattenConcat) $ eType e1 +++ eType e2)
    where
    e1 = lExpr l1
    e2 = lExpr l2
    

  flattenConcat (Concat es _) = es >>= flattenConcat
  flattenConcat e = [e]
  
  scopeConstraintNum I.PExp {I._exp = I.IInt const'} = constant const'
  scopeConstraintNum I.PExp {I._exp = I.IFunExp {I._op = "#", I._exps = [path]}} = parsePath curThis path
  scopeConstraintNum _ = mzero

  constant :: (Monad m, Integral i) => i -> m Expr
  constant = return . Const . toInteger

  greaterThan = liftM2 (,GTH,)
  greaterThanEqual = liftM2 (,GEQ,)
  lessThan = liftM2 (,LTH,)
  lessThanEqual = liftM2 (,LEQ,)
  eqTo = liftM2 (,EQU,)


{-
 - We use the stack to push every abstraction we traverse through.
 - For example:
 - 
 -  abstract A
 -    B ?
 -      C : D ?
 -  abstract D
 -    E ?
 -  F : A
 -  G : A
 -  H : A
 -
 -  [some F.B.C.E]
 -  [some G.B.C.E]
 -
 - The first constraint's final stack will look like ["C" ,"F"]
 - Hence the linear programming equation will look like:
 -
 -  scope_F_C_E >= scope_root
 -
 - Adding the second constraint:
 -
 -  scope_G_C_E >= scope_root
 -  scope_E >= scope_F_C_E + scope_G_C_E (*)
 -
 - Solving the minimization should have scope_E = 2 in its solution.
 - The (*) equation is set in constraintConstraints
 -}      
parsePath :: MonadScope m => SClafer -> I.PExp -> m Expr
parsePath start pexp =
    do
        start' <- claferWithUid (origUid start)
        parsePath2 start' pexp
 
parsePath2 :: MonadScope m => SClafer -> I.PExp -> m Expr
parsePath2 start pexp =
  do
    root <- claferWithUid rootUid
    case unfoldJoins pexp of
        Just unfold -> do
            match <- patternMatch parsePath' (ParseState root []) unfold
            either (fail . show) return match
        Nothing     -> fail "Cannot unfold."
  where
  asPath :: [[String]] -> Path
  asPath parts = Path [Part part | part <- parts, not $ null part]
  
  parsePath' = (This <$> (asPath <$> parseThisPath) <*> getThisType) <|> (Global <$> (asPath <$> parseNonthisPath) <*> getThisType)
  
  getThisType =
    do
        t <- getThis
        return $ fromJust $ fromUnionType [uid t]
  
  parseThisPath =
    do
      t <- _this_
      do
        many1 _parent_
        return [[uid start]]
        <|> (follow t >> parseNonthisPath)
  parseNonthisPath =
    do
      paths <- many (step >>= follow)
      
      lifo <- popStack
      let end = if null paths then [] else [last paths]
      let result = reverse $ end ++ map uid lifo
      
      do
        _ref_ >>= follow
        -- recurse
        rec <- parseNonthisPath
        return $ result : rec
        <|> return [result]
      
  -- Step handles non-this token.
  step :: MonadScope m => ParseT m String
  step = _parent_ <|> _directChild_ <|> try (pushThis >> _indirectChild_)
  
  -- Update the state of where "this" is.
  -- Path is one step away from where "this" is.
  follow :: MonadScope m => String -> ParseT m String
  follow path =
    do
      curThis <- getThis
      case path of
        "this" -> putThis start
        "parent" -> lift (parentOf curThis) >>= putThis -- the parent is now "this"
        "ref" -> lift (refOf curThis) >>= putThis -- the ref'd Clafer is now "this"
        u -> lift (claferWithUid u) >>= putThis
      return path



      
      
{------------------------------------------------------------
 ---------- Internals ---------------------------------------
 ------------------------------------------------------------}

newtype ScopeAnalysis a = ScopeAnalysis (VSupplyT (AnalysisT (LPM String Double)) a)
  deriving (Monad, Functor, MonadState (LP String Double), MonadSupply Var, MonadReader Info, MonadAnalysis)

class (MonadAnalysis m, MonadState (LP String Double) m, MonadSupply Var m) => MonadScope m

instance (MonadAnalysis m, MonadState (LP String Double) m, MonadSupply Var m) => MonadScope m


runScopeAnalysis :: ScopeAnalysis a -> Info -> (a, LP String Double)
runScopeAnalysis (ScopeAnalysis s) info = runLPM $ runAnalysisT (runVSupplyT s) info

-- Unfold joins
-- If the expression is a tree of only joins, then this function will flatten
-- the joins into a list.
-- Otherwise, returns an empty list.
unfoldJoins :: Monad m => I.PExp -> m [Token]
unfoldJoins pexp =
    unfoldJoins' pexp
    where
    unfoldJoins' I.PExp{I._exp = (I.IFunExp "." args)} =
        return $ args >>= (fromMaybe [] . unfoldJoins)
    unfoldJoins' I.PExp{I._inPos, I._exp = I.IClaferId{I._sident}} =
        return $ [Token (spanToSourcePos _inPos) _sident]
    unfoldJoins' _ =
        fail "not a join"


-- Variables starting with "_aux_" are reserved for creating
-- new variables at runtime.
uniqNameSpace :: String
uniqNameSpace = "_aux_"

uniqVar :: MonadScope m => m String
uniqVar =
  do
    c <- supplyNew
    return $ uniqNameSpace ++ show (varId c)

{-
 - Create a new variable "aux". If
 -   v == 0 -> aux == 0
 -   v > 0  -> aux == 1
 -
 - pre: v >= 0 and v is integer
 -}
testPositive :: MonadScope m => String -> m String
testPositive v =
  do
    aux <- uniqVar
    var aux `leq` var v
    var aux `geq` (smallM *^ var v)
    var aux `leqTo` 1
    setVarKind aux IntVar
    return aux
    
{-
 - Create a new variable "aux". If
 -   all v == 0 -> aux == 0
 -   all v > 0  -> aux == 1
 -
 - pre: all v >= 0 and all v is integer
 -}
testPositives :: MonadScope m => [String] -> m String
testPositives [v] = testPositive v
testPositives vs =
  do
    auxs <- mapM testPositive vs
    aux <- uniqVar
    (length vs *^ var aux) `equal` varSum auxs
    
    a <- uniqVar
    (var a ^-^ var aux) `geqTo` (-0.9999) -- Buffer for floating point inaccuracies
    (var a ^-^ var aux) `leqTo` 0.0001    -- Buffer for floating point inaccuracies
    setVarKind a IntVar
    return a

{-
 - smallM cannot be too small. For example, with glpk
 -   0.000001 * 9 = 0
 -}
smallM :: Double
smallM = 0.0005 -- 0.00001





{-
 -
 - Parsing
 -
 -}
data Token = Token {tPos::SourcePos, tLexeme::String} deriving Show

data ParseState = ParseState
  {psThis::SClafer, -- "this"
   psStack::[SClafer] -- the list of all the abstract Clafers traversed
   }
   deriving Show
type ParseT = ParsecT [Token] ParseState


-- Where "this" refers to.
getThis :: MonadScope m => ParseT m SClafer
getThis =
  do
    s <- getState
    return (psThis s)

-- Update where "this" refers to.
putThis :: MonadScope m => SClafer -> ParseT m ()
putThis newThis = 
  do
    state' <- getState
    putState $ state'{psThis = newThis}

popStack :: MonadScope m => ParseT m [SClafer]
popStack =
  do
    state' <- getState
    let stack = psStack state'
    putState state'{psStack = []}
    return stack

pushThis :: MonadScope m => ParseT m ()
pushThis =
  do
    state' <- getState
    putState $ state'{psStack = psThis state' : psStack state'}


-- Parser combinator for "this"
_this_ :: MonadScope m => ParseT m String
_this_ = satisfy (== "this")

-- Parser combinator for "parent"
_parent_ :: MonadScope m => ParseT m String
_parent_ = satisfy (== "parent")

-- Parser combinator for "ref"
_ref_ :: MonadScope m => ParseT m String
_ref_ = satisfy (== "ref")

-- Parser combinator for a uid that is not "this", "parent", or "ref"
_child_ :: MonadScope m => ParseT m String
_child_ = satisfy (not . (`elem` ["this", "parent", "ref"]))

-- Parser combinator for a uid of direct child.
_directChild_ :: MonadScope m => ParseT m String
_directChild_ =
  try $ do
    curThis <- getThis
    clafer <- _child_ >>= lift . claferWithUid
    check <- lift $ isDirectChild clafer curThis
    when (not check) $ unexpected $ (uid clafer) ++ " is not a direct child of " ++ (uid curThis)
    return $ uid clafer

-- Parser combinator for a uid of indirect child.
_indirectChild_ :: MonadScope m => ParseT m String
_indirectChild_ =
  try $ do
    curThis <- getThis
    clafer <- _child_ >>= lift . claferWithUid
    check <- lift $ isIndirectChild clafer curThis
    when (not check) $ unexpected $ (uid clafer) ++ " is not an indirect child of " ++ (uid curThis)
    return $ uid clafer    
    

satisfy :: MonadScope m => (String -> Bool) -> ParseT m String
satisfy f = tLexeme <$> tokenPrim (tLexeme)
                                  (\_ c _ -> tPos c)
                                  (\c -> if f $ tLexeme c then Just c else Nothing)


spanToSourcePos :: Span -> SourcePos
spanToSourcePos (Span (Pos l c) _) = (newPos "" (fromInteger l) (fromInteger c))

patternMatch :: MonadScope m => ParseT m a -> ParseState -> [Token] -> m (Either ParseError a)
patternMatch parse' state' =
  runParserT (parse' <* eof) state' ""

{-
 -
 - Utility functions
 -
 -}
 
subexpressions :: I.PExp -> [I.PExp]
subexpressions p@I.PExp{I._exp = exp'} =
  p : subexpressions' exp'
  where
  subexpressions' I.IDeclPExp{I._oDecls, I._bpexp} =
    concatMap (subexpressions . I._body) _oDecls ++ subexpressions _bpexp
  subexpressions' I.IFunExp{I._exps} = concatMap subexpressions _exps
  subexpressions' _ = []

instance MonadSupply s m => MonadSupply s (ListT m) where
  supplyNew = lift supplyNew
  
instance MonadSupply s m => MonadSupply s (MaybeT m) where
  supplyNew = lift supplyNew

instance MonadSupply s m => MonadSupply s (ParsecT a b m) where
  supplyNew = lift supplyNew
