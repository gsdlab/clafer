{-# LANGUAGE NamedFieldPuns #-}

module Language.Clafer.Generator.Choco (genCModule) where

import Language.Clafer.Intermediate.ScopeAnalyzer
import Control.Applicative
import Control.Monad
import Control.Monad.Writer
import Data.List
import Data.Maybe
import Data.Ord
import Prelude hiding (exp)
import System.Process
import Language.Clafer.ClaferArgs
import Language.Clafer.Common
import Language.Clafer.Front.Absclafer
import Language.Clafer.Intermediate.Intclafer
import Debug.Trace


genCModule :: ClaferArgs -> (IModule, GEnv) -> Result
genCModule _ (imodule@IModule{mDecls}, _) =
    genScopes
    ++ "\n"
    ++ (genAbstractClafer =<< abstractClafers)
    ++ (genConcreteClafer =<< concreteClafers)
    ++ (genRefClafer =<< clafers)
    ++ (genConstraint =<< clafers)
    where
    root :: IClafer
    root = IClafer noSpan False Nothing "root" "root" (ISuper False [PExp Nothing "" noSpan $ IClaferId "clafer" "clafer" True]) (Just (1, 1)) (0, 0) mDecls
    
    toplevelClafers = mapMaybe iclafer mDecls
    -- The sort is so that we encounter sub clafers before super clafers when abstract clafers extend other abstract clafers
    abstractClafers = reverse $ sortBy (comparing $ length . supersOf . uid) $ filter isAbstract toplevelClafers
    parentChildMap = childClafers root
    clafers = map snd parentChildMap
    concreteClafers = filter isNotAbstract clafers
    minusRoot = filter ((/= "root") . uid)
    
    claferWithUid u = fromMaybe (error $ "claferWithUid: \"" ++ u ++ "\" is not a clafer") $ find ((== u) . uid) clafers
    
    prims = ["int", "integer", "string", "real"]
    
    -- All abstract clafers u inherits
    supersOf :: String -> [String]
    supersOf u =
        case superOf u of
             Just su -> su : supersOf su
             Nothing -> []
        
    superHierarchyOf u = u : supersOf u
            
    superOf u =
        case super $ claferWithUid u of
            ISuper False [PExp{exp = IClaferId{sident}}]
                | sident == "clafer"  -> Nothing
                | sident `elem` prims -> Nothing
                | otherwise           -> Just sident
            _ -> Nothing

    superWithRef u =
        case mapMaybe refOf $ supersOf u of
             r : rs -> r
             _      -> u ++ " does not inherit a ref"
            
    refOf u =
        case super $ claferWithUid u of
            ISuper True [PExp{exp = IClaferId{sident}}] -> Just sident
            ISuper False [PExp{exp = IClaferId{sident}}]
                | sident == "int"     -> Just "integer"
                | sident `elem` prims -> Just sident
                | otherwise           -> Nothing
            _ -> Nothing
            
    -- All clafers that inherit u
    subOf :: String -> [String]
    subOf u = [uid | IClafer{uid} <- clafers, Just u == superOf uid]
    subClaferOf :: String -> [IClafer]
    subClaferOf = map claferWithUid . subOf
    
    subOffsets :: [(String, String, Integer)]
    subOffsets = [(uid, sub, off) | IClafer{uid} <- clafers, let subs = subOf uid, (sub, off) <- zip subs $ offsets subs]
    
    subOffsetOf :: String -> Integer
    subOffsetOf sub = thd3 $ fromMaybe (error $ "subOffsetOf: " ++ sub) $ find ((== sub) . snd3) subOffsets
    
    snd3 (_, b, _) = b
    thd3 (_, _, c) = c
    
    offsets :: [String] -> [Integer]
    offsets = scanl (flip $ (+) . scopeOf) 0
        

    parentOf u = fst $ fromMaybe (error $ "parentOf: \"" ++ u ++ "\" is not a clafer") $ find ((== u) . uid . snd) parentChildMap
    parentClaferOf = claferWithUid . parentOf
    -- Direct childrens
    childrenOf = map uid . childrenClaferOf
    childrenClaferOf u = [c | (p, c) <- parentChildMap, p == u]
    
    -- Indirect childrens
    indirectChildrenOf u = childrenOf =<< supersOf u
    indirectChildrenClaferOf u = childrenClaferOf =<< supersOf u
    
    isBounded :: Interval -> Bool
    isBounded (0, -1) = False
    isBounded _       = True
    
    genCard :: Interval -> Maybe String
    genCard (0, -1) = Nothing
    genCard (low, -1) = return $ show low
    genCard (low, high) = return $ show low ++ ", " ++ show high
    
    
    genScopes :: Result
    genScopes =
        "scope({" ++ intercalate ", " scopeMap ++ "});\n"
        where
            scopeMap = [uid ++ ":" ++ show (scopeOf uid) | IClafer{uid} <- concreteClafers]
                
    genConcreteClafer :: IClafer -> Result
    genConcreteClafer IClafer{uid, card = Just card, gcard = Just (IGCard _ gcard)} =
            uid ++ " = " ++ constructor ++ "(\"" ++ uid ++ "\")" ++ prop "withCard" (genCard card) ++ prop "withGroupCard" (genCard gcard) ++ prop "extending" (superOf uid) ++ ";\n"
        where
            constructor = 
                case parentOf uid of
                     "root" -> "clafer"
                     puid   -> puid ++ ".addChild"
            prop name value =
                case value of
                     Just value' -> "." ++ name ++ "(" ++ value' ++ ")"
                     Nothing     -> ""
                
                
    genRefClafer :: IClafer -> Result
    genRefClafer IClafer{uid} =
        case (refOf uid, uid `elem` uniqueRefs) of
             (Just target, True)  -> uid ++ ".refTo(" ++ genTarget target ++ ");\n"
             (Just target, False) -> uid ++ ".refToUnique(" ++ genTarget target ++ ");\n"
             _                    -> ""
        where
            genTarget "integer" = "int"
            genTarget target = target
        
    genAbstractClafer :: IClafer -> Result
    genAbstractClafer IClafer{uid, card = Just card} =
        uid ++ " = abstract(\"" ++ uid ++ "\");\n"  
    
    -- Is a uniqueness constraint? If so, return the name of unique clafer
    isUniqueConstraint :: IExp -> Maybe String
    isUniqueConstraint (IDeclPExp IAll [IDecl True [x, y] PExp{exp = IClaferId {sident}}]
        PExp{exp = IFunExp "!=" [
            PExp{exp = IFunExp "." [PExp{exp = IClaferId{sident = xident}}, PExp{exp = IClaferId{sident = "ref"}}]},
            PExp{exp = IFunExp "." [PExp{exp = IClaferId{sident = yident}}, PExp{exp = IClaferId{sident = "ref"}}]}]})
                | x == xident && y == yident = return sident
                | otherwise                  = mzero
    isUniqueConstraint  (IDeclPExp IAll [IDecl True [x, y] PExp{exp = IFunExp "." [PExp{exp = IClaferId{sident = "this"}}, PExp{exp = IClaferId {sident}}]}]
        PExp{exp = IFunExp "!=" [
            PExp{exp = IFunExp "." [PExp{exp = IClaferId{sident = xident}}, PExp{exp = IClaferId{sident = "ref"}}]},
            PExp{exp = IFunExp "." [PExp{exp = IClaferId{sident = yident}}, PExp{exp = IClaferId{sident = "ref"}}]}]})
                | x == xident && y == yident = return sident
                | otherwise                  = mzero
    isUniqueConstraint _ = mzero
    
    uniqueRefs :: [String]
    uniqueRefs = mapMaybe isUniqueConstraint $ map exp $ mapMaybe iconstraint $ clafers >>= elements
    
    genConstraint :: IClafer -> Result
    genConstraint IClafer{uid, elements} =
        unlines [uid ++ ".addConstraint(" ++ genConstraintPExp c ++ ");"
            | c <- filter (isNothing . isUniqueConstraint . exp) $ mapMaybe iconstraint elements]
            
    nameOfType TInteger = "integer"
    nameOfType (TClafer [t]) = t
    
    namesOfType TInteger = ["integer"]
    namesOfType (TClafer ts) = ts

    getCard uid =
        case card $ claferWithUid uid of
                Just (low, -1)   -> (low, scope)
                Just (low, high) -> (low, high)
        where
            scope = scopeOf uid
    
    fst3 (a, _, _) = a
    (l1, h1) <*> (l2, h2) = (l1 * l2, h1 * h2)
    scopeCap scope (l, h) = (min scope l, min scope h)
    
    rewrite :: PExp -> IExp
    -- Rearrange right joins to left joins.
    rewrite p1@PExp{iType = Just typ, exp = IFunExp "." [p2, p3@PExp{exp = IFunExp "." [p4, p5]}]} =
        IFunExp "." [p1{iType = iType p4, exp = IFunExp "." [p2, p4]}, p5]
    rewrite PExp{exp = IFunExp{op = "-", exps = [p@PExp{exp = IInt i}]}} =
        IInt (-i)
    rewrite p = exp p
    
    genConstraintPExp :: PExp -> String
    genConstraintPExp = genConstraintExp . rewrite
            
    genConstraintExp :: IExp -> String
    genConstraintExp e@(IDeclPExp INo [] body) =
        "none(" ++ genConstraintPExp body ++ ")"
             
    genConstraintExp (IFunExp "." [e1, PExp{exp = IClaferId{sident = "ref"}}]) =
        "joinRef(" ++ genConstraintPExp e1 ++ ")"
    genConstraintExp (IFunExp "." [e1, PExp{exp = IClaferId{sident = "parent"}}]) =
        "joinParent(" ++ genConstraintPExp e1 ++ ")"
    genConstraintExp (IFunExp "." [e1, PExp{exp = IClaferId{sident}}]) =
        "join(" ++ genConstraintPExp e1 ++ ", " ++ sident ++ ")"
    genConstraintExp (IFunExp "=" [e1, e2]) =
        "equal(" ++ genConstraintPExp e1 ++ ", " ++ genConstraintPExp e2 ++ ")"
    -- this is a keyword in Javascript so use "$this" instead
    genConstraintExp IClaferId{sident = "this"} = "$this()"
    genConstraintExp IClaferId{sident} = sident
    genConstraintExp (IInt val) = "constant(" ++ show val ++ ")"
    genConstraintExp e = error $ show e
                
    sidentOf u = ident $ claferWithUid u
    scopeOf "integer" = undefined
    scopeOf i = fromMaybe 1 $ lookup i scopes
    scopes = scopeAnalysis imodule
    
isQuant PExp{exp = IDeclPExp{}} = True
isQuant _ = False

isNotAbstract :: IClafer -> Bool
isNotAbstract = not . isAbstract

iclafer :: IElement -> Maybe IClafer
iclafer (IEClafer c) = Just c
iclafer _ = Nothing

iconstraint :: IElement -> Maybe PExp
iconstraint (IEConstraint _ pexp) = Just pexp
iconstraint _ = Nothing

childClafers :: IClafer -> [(String, IClafer)]
childClafers IClafer{uid, elements} =
    childClafers' uid =<< mapMaybe iclafer elements
    where
    childClafers' parent c@IClafer{uid, elements} = (parent, c) : (childClafers' uid  =<< mapMaybe iclafer elements)

implies :: MonadPlus m => Bool -> m a -> m a
implies cond result = if cond then result else mzero
