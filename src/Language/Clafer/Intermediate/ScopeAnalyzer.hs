{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}

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
module Language.Clafer.Intermediate.ScopeAnalyzer (scopeAnalysis) where

import Language.Clafer.Front.Absclafer hiding (Path)
import qualified Language.Clafer.Intermediate.Intclafer as I

import Control.Applicative hiding (Alternative(..))
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
import Language.Clafer.Intermediate.Test


{------------------------------------------------------------
 ---------- Linear programming ------------------------------
 ------------------------------------------------------------}

scopeAnalysis :: I.IModule -> [(String, Integer)]
scopeAnalysis imodule =
  removeZeroes $ removeRoot $ removeAux $
    -- unsafePerformIO should be safe (?)
    -- We aren't modifying any global state.
    -- If we don't use unsafePerformIO, then we have to be inside the IO monad and
    -- makes things really ugly. Might as well contain the ugliness in here.
    case unsafePerformIO solution of
      (Success, Just (_, s)) -> Map.toList $ Map.map round s
      _ -> [] -- No solution
  where
  (abstracts, analysis) = runAnalysis (setConstraints >> (clafers `suchThat` isAbstract)) $ gatherInfo imodule
  solution = glpSolveVars mipDefaults{msgLev = MsgOff} $ analysis
  -- Any scope that is 0 will take the global scope of 1 instead.
  removeZeroes = filter ((/= 0) . snd)
  -- The root is implied and not and not part of the actual solution.
  removeRoot = filter ((/= rootUid) . fst)
  -- Auxilary variables are only part of the computation, not the solution.
  removeAux = filter (not . (uniqNameSpace `isPrefixOf`) . fst)
  -- The scope for abstract clafers are removed. Alloy doesn't need it. Makes
  -- it easier use since user can increase the scope of subclafers without
  -- needing to increase the scope of the abstract Clafer.
  removeAbstracts = filter (not . (`elem` map uid abstracts) . fst)

setConstraints :: Analysis ()
setConstraints =
  do
    reifyClafers <- constraintConstraints
    withExtraClafers reifyClafers $ do
      optFormula
      colonConstraints
      refConstraints
      parentConstraints

    (var rootUid) `equalTo` 1


optFormula :: Analysis ()
optFormula =
  do
    setDirection Min
    c <- clafers
    let concretes = [uid concrete | concrete <- c, not $ isAbstract concrete]
    setObjective $ varSum concretes

parentConstraints :: Analysis ()
parentConstraints =
  runListT_ $ do
    -- forall child under parent ...
    (child, parent) <- foreach $ anything |^ anything

    let uchild = uid child
    let uparent = uid parent
    
    -- ... scope_this <= scope_parent * low-card(this) ...
    var uchild `geq` (low child *^ var uparent)
    -- ... scope_this >= scope_parent * high-card(this) ...
    -- high == -1 implies high card is unbounded

    if high child /= -1
      then var uchild `leq` (high child *^ var uparent)
      else (smallM *^ var uchild) `leq`var uparent
    -- Use integer's not doubles
    setVarKind uchild IntVar
    setVarKind uparent IntVar


refConstraints :: Analysis ()
refConstraints =
  runListT_ $ do
    -- for all uids of any clafer the refs another uid ...
    (sub, sup) <- foreach $ anything |-> anything
    let usub = uid sub
    let usup = uid sup
    aux <- testPositive usub
    -- scope_sup >= low-card(sub)
    var usup `geq` ((max 1 $ low sub) *^ var aux)


colonConstraints :: Analysis ()
colonConstraints =
  runListT_ $ do
    -- forall c in the set of clafers' uid ...
    c <- foreach $ clafers
    -- ... find all uids of any clafer that extends c (only colons) ...
    subs <- findAll $ (anything |: c) `select` (uid . subClafers)
    when (not $ null subs) $
      -- ... then set the constraint scope_C = sum scope_subs
      var (uid c) `equal` varSum subs


data Path =
  Path {parts::[Part]}
  deriving (Eq, Ord, Show)

data Part =
  Part {steps::[String]}
  deriving (Eq, Ord, Show)

-- Returns a list of reified clafers.
constraintConstraints :: Analysis [SClafer]
constraintConstraints =
  do  
    pathList <- runListT $ do
      -- for all constraints ...
      (curThis, con) <- foreach $ constraintsUnder anything
      -- ... parse constraint expression ...
      (path, mult) <- foreach $ constraintConstraints' curThis (I.exp con)
      
      -- ... set the linear programming equations
      -- The first part is owned by curThis. The rest of the parts are after refs.
      let conc = head $ parts path
      let refs = tail $ parts path
      
      var (reifyVar conc) `geq` (mult *^ var (uid curThis))

      forM refs $
        \part -> var (reifyVar part) `geqTo` fromInteger (low curThis)
      
      return path
    
    rPartList <- forM [steps parts' | parts' <- pathList >>= parts] $
      \(conc : abst) -> do
        reifiedParts <- forM (tail $ inits abst) $
          \abst' -> reifyPart (Part $ conc : abst')
        return (conc, concat reifiedParts)
    
    -- Create reified clafers.
    runListT $ do
      (conc, parts) <- foreachM $ nub rPartList
      (parent, child) <- foreachM $ zip (Part [conc] : parts) parts
      baseClafer <- lift $ claferWithUid $ base child
      return $ SClafer (reifyVar child) False (low baseClafer) (high baseClafer) (Just $ reifyVar parent) (Just $ Colon $ uid baseClafer) []
  where 
  base (Part steps) = last steps

  reifyVar (Part [target]) = target
  reifyVar (Part target) = uniqNameSpace ++ "reify_" ++ intercalate "_" target
  
  reifyPart :: Part -> Analysis [Part]
  reifyPart (Part steps) =
    do
      as <- claferWithUid (last steps) >>= nonTopAncestors
      forM as $
        \a -> return $ Part $ init steps ++ [uid a]
  
  nonTopAncestors :: SClafer -> Analysis [SClafer]
  nonTopAncestors child =
    do
      parent <- parentOf child
      if uid parent == rootUid
        then return []
        else (++ [child]) `fmap` nonTopAncestors parent
  
  -- Does the work for one constraint.
  constraintConstraints' :: MonadAnalysis m => SClafer -> I.IExp -> m [(Path, Double)]
  constraintConstraints' curThis iexp =
    runListT $ do
      (path, mult) <- pathAndMult iexp
      p <- Path <$> (map reify <$> parsePath curThis path)
      return (p, mult)

  -- [some my.path.expression]
  --   => #my.path.expression >= 1
  pathAndMult :: (MonadPlus m, MonadAnalysis m) => I.IExp -> m (I.PExp, Double)
  pathAndMult I.IDeclPExp {I.quant = I.ISome, I.oDecls = [], I.bpexp} = return (bpexp, 1)
  -- [some disj a;b : my.path.expression | ...]
  --   => my.path.expression >= 2
  pathAndMult I.IDeclPExp {I.quant = I.ISome, I.oDecls} = msum $ map (return . pathAndMultDecl) oDecls
    where
    pathAndMultDecl :: I.IDecl -> (I.PExp, Double)
    pathAndMultDecl I.IDecl {I.isDisj = True, I.decls , I.body} = (body, fromIntegral $ length decls)
    pathAndMultDecl I.IDecl {I.isDisj = False, I.decls , I.body} = (body, 1)
    
  -- [one my.path.expression]
  --   => #my.path.expression >= 1
  pathAndMult I.IDeclPExp {I.quant = I.IOne, I.oDecls = [], I.bpexp} = return (bpexp, 1)
  pathAndMult I.IDeclPExp {I.quant = I.IOne, I.oDecls} = msum $ [return $ (I.body oDecl, 1) | oDecl <- oDecls]
  
  -- [#my.path.expression = const]
  --   => #my.path.expression >= const
  pathAndMult I.IFunExp {I.op = "=", I.exps = [I.PExp {I.exp = I.IFunExp {I.op = "#", I.exps = [path]}}, I.PExp {I.exp = I.IInt const}]} =
    return (path, fromInteger const)
  -- [const = #my.path.expression]
  --   => #my.path.expression >= const
  pathAndMult I.IFunExp {I.op = "=", I.exps = [I.PExp {I.exp = I.IInt const}, I.PExp {I.exp = I.IFunExp {I.op = "#", I.exps = [path]}}]} =
    return (path, fromInteger const)

  
  -- All quantifiers can be true even if scope is 0
  pathAndMult (I.IDeclPExp {I.quant = I.IAll}) = fail "No path."
  pathAndMult e = fail $ "TODO::" ++ show e

  reify :: [String] -> Part
  reify []  = error "Empty path." -- Bug, should never happen.
  reify xs  = Part xs


parsePath :: MonadAnalysis m => SClafer -> I.PExp -> m [[String]]
parsePath start pexp =
  do
    match <- patternMatch parsePath' (ParseState start []) (fromMaybe [] $ unfoldJoins pexp)
    case match of
      Left err -> fail $ show err
      Right s -> return $ filter (not . null) s
  where
  parsePath' =
    do
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
      paths <- many (step >>= follow)
      
      lifo <- popStack
      let end = if null paths then [] else [last paths]
      let result = reverse $ end ++ map uid lifo
      
      do
        _ref_ >>= follow
        -- recurse
        rec <- parsePath'
        return $ result : rec
        <|> return [result]
      
  -- Step handles non-this token.
  step :: MonadAnalysis m => ParseT m String
  step = _this_ <|> _directChild_ <|> try (pushThis >> _indirectChild_)
  
  -- Update the state of where "this" is.
  -- Path is one step away from where "this" is.
  follow :: MonadAnalysis m => String -> ParseT m String
  follow path =
    do
      curThis <- getThis
      case path of
        "this" -> return () -- didn't move anywhere, don't change anything
        "parent" -> parentOf curThis >>= putThis -- the parent is now "this"
        "ref" -> refOf curThis >>= putThis -- the ref'd Clafer is now "this"
        u -> claferWithUid u >>= putThis
      return path



      
      
{------------------------------------------------------------
 ---------- Internals ---------------------------------------
 ------------------------------------------------------------}

newtype Analysis a = Analysis (VSupplyT (ReaderT Info (LPM String Double)) a)
  deriving (Monad, Functor, MonadState (LP String Double), MonadSupply Var, MonadReader Info)

class (Functor m, MonadSupply Var m, MonadReader Info m, MonadState (LP String Double) m) => MonadAnalysis m

instance (Functor m, MonadSupply Var m, MonadReader Info m, MonadState (LP String Double) m) => MonadAnalysis m

  
data SSuper = Ref String | Colon String deriving Show
-- Easier to work with. IClafers have links from parents to children. SClafers have links from children to parent.
data SClafer = SClafer {uid::String, isAbstract::Bool, low::Integer, high::Integer, parent::Maybe String, super::Maybe SSuper, constraints::[I.PExp]} deriving Show

data Info = Info{sclafers :: [SClafer]} deriving Show 


runAnalysis :: Analysis a -> Info -> (a, LP String Double)
runAnalysis (Analysis s) info = runLPM $ runReaderT (runVSupplyT s) info

withExtraClafers :: MonadAnalysis m => [SClafer] -> m a -> m a
withExtraClafers extra = local addInfo
  where
  addInfo (Info c) = Info $ c ++ extra

clafers :: MonadAnalysis m => m [SClafer]
clafers = asks sclafers

claferWithUid :: MonadAnalysis m => String -> m SClafer
claferWithUid u =
  do
    c <- clafers
    case find ((==) u . uid) c of
      Just c' -> return $ c'
      Nothing -> fail $ "Unknown uid " ++ u
      
parentUid :: Monad m => SClafer -> m String
parentUid clafer =
  case parent clafer of
    Just p  -> return p
    Nothing -> fail $ "No parent uid for " ++ show clafer
    
parentOf :: MonadAnalysis m => SClafer -> m SClafer
parentOf clafer = claferWithUid =<< parentUid clafer

refUid :: Monad m => SClafer -> m String
refUid clafer =
  case super clafer of
    Just (Ref u)  -> return u
    _             -> fail $ "No ref uid for " ++ show clafer

refOf :: MonadAnalysis m => SClafer -> m SClafer
refOf clafer =  claferWithUid =<< refUid clafer

colonUid :: Monad m => SClafer -> m String
colonUid clafer =
  case super clafer of
    Just (Colon u)  -> return u
    _               -> fail $ "No colon uid for " ++ show clafer

colonOf :: MonadAnalysis m => SClafer -> m SClafer
colonOf clafer =  claferWithUid =<< colonUid clafer


{-
 - C is a direct child of B.
 -
 -  B
 -    C
 -}
isDirectChild :: MonadAnalysis m => SClafer -> SClafer -> m Bool
isDirectChild child parent = is (not . null) (child |^ parent)
 
{-
 - C is an direct child of B.
 -
 -  abstract A
 -    C
 -  B : A
 -}
isIndirectChild :: MonadAnalysis m => SClafer -> SClafer -> m Bool
isIndirectChild child parent =
  fromMaybeT False $ do
    s <- colonOf parent
    when (uid s == "clafer") mzero
    isChildren child s

isChildren :: MonadAnalysis m => SClafer -> SClafer -> m Bool
isChildren child parent =
  liftM2 (||) (isDirectChild child parent) (isIndirectChild child parent)


data Uid = Uid String | Any deriving Show

class Uidable u where
  toUid :: u -> Uid
  
instance Uidable Uid where
  toUid = id
  
instance Uidable SClafer where
  toUid = Uid . uid

matches :: Uid -> String -> Bool
matches (Uid u1) u2 = u1 == u2
matches Any _ = True

anything :: Uid
anything = Any


-- a is a child of b
(|^) :: (MonadAnalysis m, Uidable a, Uidable b) => a -> b -> m [(SClafer, SClafer)]
lower |^ upper =
  runListT $ do
    clafer <- foreach clafers
    parent <- parentOf clafer
    when (not $ matches (toUid lower) (uid clafer)) mzero
    when (not $ matches (toUid upper) (uid parent)) mzero
    return (clafer , parent)

-- a -> b    
(|->) :: (MonadAnalysis m, Uidable a, Uidable b) => a -> b -> m [(SClafer, SClafer)]
lower |-> upper =
  runListT $ do
    clafer <- foreach clafers
    super  <- refOf clafer
    when (not $ matches (toUid lower) (uid clafer)) mzero
    when (not $ matches (toUid upper) (uid super)) mzero
    return (clafer, super)

-- a : b
(|:) :: (MonadAnalysis m, Uidable a, Uidable b) => a -> b -> m [(SClafer, SClafer)]
lower |: upper =
  runListT $ do
    clafer <- foreach clafers
    super  <- colonOf clafer
    when (not $ matches (toUid lower) (uid clafer)) mzero
    when (not $ matches (toUid upper) (uid super)) mzero
    return (clafer, super)

-- constraints under
constraintsUnder :: (MonadAnalysis m, Uidable a) => a -> m [(SClafer, I.PExp)]
constraintsUnder under =
  runListT $ do
    clafer <- foreach clafers
    when (not $ matches (toUid under) (uid clafer)) mzero
    constraint <- foreachM $ constraints clafer
    return (clafer, constraint)


rootUid :: String
rootUid = "_root"

-- Converts IClafer to SClafer
convertClafer :: I.IClafer -> [SClafer]
convertClafer = 
  convertClafer' Nothing
  where
  convertElement' parent (I.IEClafer clafer) = Just $ Left $ convertClafer' parent clafer
  convertElement' _ (I.IEConstraint _ pexp)   = Just $ Right $ pexp
  convertElement' _ _ = Nothing
  
  convertClafer' parent clafer =
    SClafer (I.uid clafer) (I.isAbstract clafer) low high parent super constraints : concat children
    where
    (children, constraints) = partitionEithers $ mapMaybe (convertElement' $ Just $ I.uid clafer) (I.elements clafer)
    
    Just (low, high) = I.card clafer
    super =
      case I.super clafer of
        I.ISuper True [I.PExp{I.exp = I.IClaferId{I.sident = superUid}}]  -> Just $ Ref superUid
        I.ISuper False [I.PExp{I.exp = I.IClaferId{I.sident = superUid}}] -> Just $ Colon superUid
        _ -> Nothing

gatherInfo :: I.IModule -> Info
gatherInfo imodule =
  Info $ convertClafer root
  where
  root = I.IClafer noSpan True Nothing rootUid rootUid (I.ISuper False [I.PExp Nothing "" noSpan $ I.IClaferId "clafer" "clafer" True]) (Just (1, 1)) (0, 0) $ I.mDecls imodule

-- Unfold joins
-- If the expression is a tree of only joins, then this function will flatten
-- the joins into a list.
-- Otherwise, returns an empty list.
unfoldJoins :: Monad m => I.PExp -> m [Token]
unfoldJoins pexp =
    unfoldJoins' pexp
    where
    unfoldJoins' I.PExp{I.exp = (I.IFunExp "." args)} =
        return $ args >>= (fromMaybe [] . unfoldJoins)
    unfoldJoins' I.PExp{I.inPos, I.exp = I.IClaferId{I.sident}} =
        return $ [Token (spanToSourcePos inPos) sident]
    unfoldJoins' _ =
        fail "not a join"


-- Variables starting with "_aux_" are reserved for creating
-- new variables at runtime.
uniqNameSpace :: String
uniqNameSpace = "_aux_"

uniqVar :: MonadAnalysis m => m String
uniqVar =
  do
    c <- supplyNew
    return $ uniqNameSpace ++ show (varId c)

{-
 - Create a new variable "aux". If
 -   v == 0 -> aux == 0
 -   v > 0  -> aux == 1
 -
 - pre: v >= 0
 -}
testPositive :: MonadAnalysis m => String -> m String
testPositive v =
  do
    aux <- uniqVar
    var aux `leq` var v
    var aux `geq` (smallM *^ var v)
    var aux `leqTo` 1
    setVarKind aux IntVar
    return aux

{-
 - smallM cannot be too small. For example, with glpk
 -   0.000001 * 9 = 0
 -}
smallM :: Double
smallM = 0.00001





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
getThis :: MonadAnalysis m => ParseT m SClafer
getThis =
  do
    s <- getState
    return (psThis s)

-- Update where "this" refers to.
putThis :: MonadAnalysis m => SClafer -> ParseT m ()
putThis newThis = 
  do
    state' <- getState
    putState $ state'{psThis = newThis}

popStack :: MonadAnalysis m => ParseT m [SClafer]
popStack =
  do
    state' <- getState
    let stack = psStack state'
    putState state'{psStack = []}
    return stack

pushThis :: MonadAnalysis m => ParseT m ()
pushThis =
  do
    state' <- getState
    putState $ state'{psStack = psThis state' : psStack state'}


-- Parser combinator for "this"
_this_ :: MonadAnalysis m => ParseT m String
_this_ = satisfy (== "this")

-- Parser combinator for "parent"
_parent_ :: MonadAnalysis m => ParseT m String
_parent_ = satisfy (== "parent")

-- Parser combinator for "ref"
_ref_ :: MonadAnalysis m => ParseT m String
_ref_ = satisfy (== "ref")

-- Parser combinator for a uid that is not "this", "parent", or "ref"
_child_ :: MonadAnalysis m => ParseT m String
_child_ = satisfy (not . (`elem` ["this", "parent", "ref"]))

-- Parser combinator for a uid of direct child.
_directChild_ :: MonadAnalysis m => ParseT m String
_directChild_ =
  try $ do
    curThis <- getThis
    clafer <- _child_ >>= claferWithUid
    check <- isDirectChild clafer curThis
    when (not check) $ unexpected $ (uid clafer) ++ " is not a direct child of " ++ (uid curThis)
    return $ uid clafer

-- Parser combinator for a uid of indirect child.
_indirectChild_ :: MonadAnalysis m => ParseT m String
_indirectChild_ =
  try $ do
    curThis <- getThis
    clafer <- _child_ >>= claferWithUid
    check <- isIndirectChild clafer curThis
    when (not check) $ unexpected $ (uid clafer) ++ " is not an indirect child of " ++ (uid curThis)
    return $ uid clafer    
    

satisfy :: MonadAnalysis m => (String -> Bool) -> ParseT m String
satisfy f = tLexeme <$> tokenPrim (tLexeme)
                                  (\_ c _ -> tPos c)
                                  (\c -> if f $ tLexeme c then Just c else Nothing)


spanToSourcePos :: Span -> SourcePos
spanToSourcePos (Span (Pos l c) _) = (newPos "" (fromInteger l) (fromInteger c))


patternMatch :: MonadAnalysis m => ParseT m a -> ParseState -> [Token] -> m (Either ParseError a)
patternMatch parse' state' =
  runParserT (parse' <* eof) state' ""



{-
 -
 - Utility functions
 -
 -}
runListT_ :: Monad m => ListT m a -> m ()
runListT_ l = runListT l >> return ()

foreach :: m[a] -> ListT m a
foreach = ListT

foreachM :: Monad m => [a] -> ListT m a
foreachM = ListT . return


subClafers :: (a, b) -> a
subClafers = fst

findAll :: Monad m => m a -> ListT m a
findAll = lift

select :: Monad m => m [a] -> (a -> b) -> m [b]
select from f = from >>= return . map f

is :: Monad m => (a -> Bool) -> m a -> m Bool
is = liftM

suchThat :: Monad m => m [a] -> (a -> Bool) -> m [a]
suchThat = flip $ liftM . filter

fromMaybeT :: Monad m => a -> MaybeT m a -> m a
fromMaybeT def m = fromMaybe def `liftM` runMaybeT m


instance MonadSupply s m => MonadSupply s (ListT m) where
  supplyNew = lift supplyNew
  
instance MonadSupply s m => MonadSupply s (MaybeT m) where
  supplyNew = lift supplyNew

instance MonadSupply s m => MonadSupply s (ParsecT a b m) where
  supplyNew = lift supplyNew
