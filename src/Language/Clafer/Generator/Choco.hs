{-# LANGUAGE NamedFieldPuns #-}

module Language.Clafer.Generator.Choco (genCModule) where

import Language.Clafer.Intermediate.ScopeAnalyzer
import Control.Monad
import Control.Monad.Writer
import Data.List
import Data.Maybe
import Prelude hiding (exp)
import System.Process
import Language.Clafer.ClaferArgs
import Language.Clafer.Common
import Language.Clafer.Front.Absclafer
import Language.Clafer.Intermediate.Intclafer
import Debug.Trace


genCModule :: ClaferArgs -> (IModule, GEnv) -> Result
genCModule _ (imodule@IModule{mDecls}, _) =
    "// Scopes\n"
    ++ genScopes
    ++ "var scope__low__integer = -10000;\n"
    ++ "var scope__high__integer = 10000;\n"
    ++ "\n"
    ++ "// Offsets\n"
    ++ genOffsets
    ++ "\n"
    ++ (genConcreteClafer =<< clafers)
    ++ (genAbstractClafer =<< abstractClafers)
    ++ (genCardinality =<< clafers)
    ++ (genGroupCardinality =<< clafers)
    ++ (genRefClafer =<< clafers)
    ++ (genConstraint =<< clafers)
    -- "Prints the solution.
    ++ "function solution() {\n"
    ++ "    solution__root(0, \"\");\n"
    ++ "}\n"
    ++ "\n"
    ++ (genToString =<< clafers)
    where
    root :: IClafer
    root = IClafer noSpan False Nothing "root" "root" (ISuper False [PExp Nothing "" noSpan $ IClaferId "clafer" "clafer" True]) (Just (1, 1)) (0, 0) mDecls
    
    toplevelClafers = mapMaybe iclafer mDecls
    abstractClafers = filter isAbstract toplevelClafers
    parentChildMap = childClafers root
    clafers = root : map snd parentChildMap
    concreteClafers = filter (not . isAbstract) clafers
    minusRoot = filter ((/= "root") . uid)
    
    claferWithUid u = fromMaybe (error $ "claferWithUid: \"" ++ u ++ "\" is not a clafer") $ find ((== u) . uid) clafers
    
    prims = ["int", "integer", "string", "real"]
    
    -- All abstract clafers u inherits
    supersOf u =
        case superOf u of
             Just su -> su : supersOf su
             Nothing -> []
        
            
    superOf u =
        case super $ claferWithUid u of
            ISuper False [PExp{exp = IClaferId{sident}}]
                | sident == "clafer"  -> Nothing
                | sident `elem` prims -> Nothing
                | otherwise           -> Just sident
            _ -> Nothing
            
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
    
    -- Guesses the size of the set of the expression. Returns a lower and upper bound.
    guessSize :: PExp -> (Integer, Integer)
    guessSize PExp{exp} =
        case exp of
             IFunExp "." [arg1, PExp{exp = IClaferId{sident = arg2}}]
                                      -> guessSize arg1 <*> getCard arg2
             IFunExp "." [arg1, arg2] -> guessSize arg1 <*> guessSize arg2
             IClaferId{sident}        -> (0, scopeOf sident)
             IInt _                   -> (1, 1)
        where
            getCard uid =
                case card $ claferWithUid uid of
                     Just (low, -1)   -> (min low scope, scope)
                     Just (low, high) -> (min low scope, min high scope)
                where
                    scope = scopeOf uid
            (l1, h1) <*> (l2, h2) = (l1 * l2, h1 * h2)
                 
    
    genScopes :: Result
    genScopes =
        do
            IClafer{uid} <- clafers
            "var scope__" ++ uid ++ " = " ++ show (scopeOf uid) ++ ";\n"
                ++ "var scope__low__" ++ uid ++ " = 0;\n"
                ++ "var scope__high__" ++ uid ++ " = " ++ show (scopeOf uid - 1) ++ ";\n"
    genOffsets :: Result
    genOffsets = concat ["var offset__" ++ sub ++ " = " ++ show off ++ ";\n" | (sup, sub, off) <- subOffsets]
    
    genConcreteClafer :: IClafer -> Result
    genConcreteClafer IClafer{uid} =
        do
            IClafer{isAbstract, uid = cuid, card}  <- childrenClaferOf uid
            let name = "__" ++ cuid
            "// Clafer - " ++ uid ++ "/" ++ cuid ++ "\n"
                ++ cuid ++ " = set(\"" ++ cuid ++ "\", 0, scope__high__" ++ cuid ++ ");\n"
                ++ not isAbstract `implies`
                        (name ++ " = setArray(\"" ++ name ++ "\", scope__" ++ uid ++ ", 0, scope__high__" ++ cuid ++ ");\n"
                        ++ "addConstraint(setUnion(" ++ name ++ ", " ++ cuid ++ "));\n"
                        ++ cuid ++ "__parent = intArray(\"" ++ cuid ++ "__parent\", scope__" ++ cuid ++ ", 0, scope__" ++ uid ++ ");\n"
                        ++ "addConstraint(inverseSet(" ++ cuid ++ "__parent, " ++ name ++ ".concat(setArray(\"" ++ name ++ "__unused\", 1, 0, scope__high__" ++ cuid ++ "))));\n")
                ++ "\n"
                
    genRefClafer :: IClafer -> Result
    genRefClafer IClafer{uid} =
        fromMaybe "" $ do
            ref <- refOf uid
            return $
                name ++ " = intArray(\"" ++ name ++ "\", scope__" ++ uid ++ ", scope__low__" ++ ref ++ ", scope__high__" ++ ref ++ ");\n"
                ++ "addVariable(" ++ name ++ ");\n"
        where
            name = uid ++ "__ref"
            parent = uid ++ "__parent"
        
    genAbstractClafer :: IClafer -> Result
    genAbstractClafer IClafer{uid} =
        "// Abstract - " ++ uid ++ "\n"
        ++ concat [channel sup sub | (sup, sub, _) <- subOffsets]
        where
            channel sup sub =
                "for (var i = 0; i < scope__" ++ sub ++ "; i++) {\n"
                ++ "    addConstraint(ifOnlyIf(member(i, " ++ sub ++ "), member(i + offset__" ++ sub ++ ", " ++ sup ++ ")));\n"
                ++ "}\n"
                ++ "\n"
        
    genCardinality IClafer{uid} =
        do
            IClafer{isAbstract, uid = cuid, card = Just card}  <- childrenClaferOf uid
            guard $ not isAbstract
            let name = "__" ++ cuid
            "// Child - " ++ uid ++ "/" ++ cuid ++ " " ++ show card ++ "\n"
                ++ "for (var i = 0; i < " ++ name ++ ".length; i++) {\n"
                ++
                    case card of
                        (low, -1)   ->
                            "    addConstraint(implies(member(i , " ++ uid ++ "), geqCard(" ++ name ++ "[i], " ++ show low ++ ")));\n"
                        (low, high)
                            | low == high ->
                                "    addConstraint(implies(member(i, " ++ uid ++ "), eqCard(" ++ name ++ "[i], " ++ show low ++ ")));\n"
                            | otherwise   ->
                                "    addConstraint(implies(member(i, " ++ uid ++ "), and([geqCard(" ++ name ++ "[i], " ++ show low ++ "), leqCard(" ++ name ++ "[i], " ++ show high ++ ")])));\n"
                ++ "    addConstraint(implies(notMember(i, " ++ uid ++ "), eqCard(" ++ name ++ "[i], 0)));\n"
                ++ "}\n"
                ++ "\n"

    genGroupCardinality IClafer{gcard = Nothing} = ""
    genGroupCardinality IClafer{uid, gcard = Just (IGCard _ card)}
        | length children > 0 =
            case genGroupCardinality' (fst card) (snd card) of
                Just group ->
                    "for (var i = 0; i < scope__" ++ uid ++ "; i++) {\n"
                    ++ group
                    ++ "}\n"
                Nothing -> ""
        | otherwise = ""
        where
        genGroupCardinality' 0 (-1) = Nothing
        genGroupCardinality' 0 high = Just $ "    addConstraint(implies(member(i, " ++ uid ++ "), leq(" ++ childrenUnion ++ ", " ++ asNumber high ++ ")));\n"
        genGroupCardinality' low high = Just $ "    addConstraint(implies(member(i, " ++ uid ++ "), between(" ++ asNumber low ++ ", " ++ childrenUnion ++ ", " ++ asNumber high ++ ")));\n"

        children = childrenOf uid
        childrenUnion = "sum([" ++ (intercalate ", " $ ["__" ++ child ++ "[i].getCard()" | child <- children]) ++ "])"

    asNumber (-1) = "Number.POSITIVE_INFINITY"
    asNumber num = show num

    genUniqueConstraint :: String -> Result
    genUniqueConstraint uid =
        "uniqueRef(" ++ parent ++ ", scope__" ++ parentOf uid ++ ", " ++ name ++ ")"
        where
            name = uid ++ "__ref"
            parent = uid ++ "__parent"
    
    genConstraint :: IClafer -> Result
    genConstraint IClafer{uid, elements} =
        "for (var __this = 0; __this < scope__" ++ uid ++ "; __this++) {\n"
        ++ unlines ["    addConstraint(" ++  c ++ ");" | c <- constraint =<< mapMaybe iconstraint elements]
        ++ "}\n"
        where
            constraint c = ["implies(member(__this, " ++ uid ++ "), " ++ c' ++ ")" | c' <- genConstraint' c]
        
    nameOfType TInteger = "integer"
    nameOfType (TClafer [t]) = t
        
    genConstraint' :: PExp -> [String]
    -- Rearrange right joins to left joins.
    genConstraint' p1@PExp{exp = IFunExp "." [p2, p3@PExp{exp = IFunExp "." [p4, p5]}]} =
        genConstraintExp $ IFunExp "." [p1{iType = iType p4, exp = IFunExp "." [p2, p4]}, p5]
    genConstraint' PExp{exp} = genConstraintExp exp
        
    genConstraintExp :: IExp -> [String]
    -- Special constraint for references.
    -- Optimize!
    genConstraintExp (IDeclPExp IAll [IDecl True [x, y]  PExp{exp = IClaferId {sident}}]
        PExp{exp = IFunExp "!=" [
            PExp{exp = IFunExp "." [PExp{exp = IClaferId{sident = xident}}, PExp{exp = IClaferId{sident = "ref"}}]},
            PExp{exp = IFunExp "." [PExp{exp = IClaferId{sident = yident}}, PExp{exp = IClaferId{sident = "ref"}}]}]})
                | x == xident && y == yident = [genUniqueConstraint sident]
                | otherwise                  = error "TODO:genConstraint"
    genConstraintExp (IDeclPExp IAll [IDecl True [x, y] 
        PExp{exp = IFunExp "." [PExp{exp = IClaferId{sident = "this"}}, PExp{exp = IClaferId {sident}}]}]
        PExp{exp = IFunExp "!=" [
            PExp{exp = IFunExp "." [PExp{exp = IClaferId{sident = xident}}, PExp{exp = IClaferId{sident = "ref"}}]},
            PExp{exp = IFunExp "." [PExp{exp = IClaferId{sident = yident}}, PExp{exp = IClaferId{sident = "ref"}}]}]})
                | x == xident && y == yident = [genUniqueConstraint sident]
                | otherwise                  = error "TODO:genConstraint"
    genConstraintExp (IDeclPExp ISome [] b) =
        do
            b' <- genConstraint' b
            return $ "geqCard(" ++ b' ++ ", 1)"
    genConstraintExp (IDeclPExp INo [] b) =
        do
            b' <- genConstraint' b
            return $ "eqCard(" ++ b' ++ ", 0)"
    genConstraintExp (IFunExp "#" [arg]) =
        do
            arg' <- genConstraint' arg
            return $ "singleton(" ++ arg' ++ ".getCard())"
    genConstraintExp (IFunExp "=" [arg1, arg2]) =
        do
            arg1' <- genConstraint' arg1
            arg2' <- genConstraint' arg2
            return $ "eq(" ++ arg1' ++ ", " ++ arg2' ++ ")";
    genConstraintExp (IFunExp "." [arg1@PExp{iType = Just t1}, PExp{iType = Just t2, exp = IClaferId{sident = "parent"}}]) =
        do
            let t1' = nameOfType t1
            let t2' = nameOfType t2
            arg1' <- genConstraint' arg1
            return $ "joinParent(" ++ arg1' ++ ", scope__" ++ t1' ++ ", " ++ t1' ++ "__parent, scope__" ++ t2' ++ ")"
    -- Optimize!
    genConstraintExp (IFunExp "." [PExp{iType = Just (TClafer [t]), exp = IClaferId{sident = "this"}}, PExp{exp = IClaferId{sident = "ref"}}]) =
        ["singleton(" ++ t ++ "__ref[__this])"]
    -- Optimize!
    genConstraintExp (IFunExp "." [PExp{exp = IClaferId{sident = "this"}}, PExp{exp = IClaferId{sident = child}}]) =
        ["__" ++ child ++ "[__this]"]
    genConstraintExp k@(IFunExp "." [arg1@PExp{iType = Just (TClafer [t1])}, PExp{iType = Just t2, exp = IClaferId{sident = "ref"}}]) =
        do
            let t2' = nameOfType t2
            arg1' <- genConstraint' arg1
            return $ "joinRef(" ++ arg1' ++ ", scope__" ++ t1 ++ ", " ++ t1 ++ "__ref" ++ ", scope__low__" ++ t2' ++ ", scope__high__" ++ t2' ++ ")"
    genConstraintExp (IFunExp "." [arg1@PExp{iType = Just (TClafer [t1])}, PExp{exp = IClaferId{sident}}]) =
        do
            arg1' <- genConstraint' arg1
            return $ "joinChild(" ++ arg1' ++ ", scope__" ++ t1 ++ ", __" ++ sident ++ ", scope__" ++ sident ++ ")"
    genConstraintExp (IFunExp "=>" [arg1, arg2]) =
        do
            arg1' <- genConstraint' arg1
            arg2' <- genConstraint' arg2
            return $ "implies(" ++ arg1' ++ ", " ++ arg2' ++ ")"
    genConstraintExp (IFunExp "<=>" [arg1, arg2]) =
        do
            arg1' <- genConstraint' arg1
            arg2' <- genConstraint' arg2
            return $ "ifOnlyIf(" ++ arg1' ++ ", " ++ arg2' ++ ")"
    genConstraintExp (IFunExp "&&" [arg1, arg2]) =
        do
            arg1' <- genConstraint' arg1
            arg2' <- genConstraint' arg2
            return $ "and([" ++ arg1' ++ ", " ++ arg2' ++ "])"
    genConstraintExp IClaferId{sident = "this"} = return "constant([__this])"
    genConstraintExp IClaferId{sident} = return sident
    genConstraintExp (IInt i) = ["constant([" ++ show i ++ "])"]
    genConstraintExp e = error $ "genConstraint: " ++ show e
    
    genConstraintSet iexp = ""
            
    

    genToString :: IClafer -> Result
    genToString c@IClafer{isAbstract = False, ident, uid = puid, elements} =
        "function solution__" ++ puid ++ "(parent, indent) {\n"
        ++ "    var i = getVar(__" ++ puid ++ "[parent]).getValue();\n"
        ++ "    for (var j in i) {\n"
        ++ "        var k = i[j];\n"
        ++ "        println(indent + \"" ++ ident ++ "\" + k);\n"
        ++ genSuperString puid
        ++ genChildrenString puid
        ++ genRefString puid
        ++ "    }\n"
        ++ "}\n"
        ++ "\n"
    genToString c@IClafer{isAbstract = True, ident, uid = puid, elements} =
        "function solution__" ++ puid ++ "(k, indent) {\n"
        ++ genSuperString puid
        ++ genChildrenString puid
        ++ genRefString puid
        ++ "}\n"
        ++ "\n"
    
    genSuperString :: String -> Result
    genSuperString puid =
        fromMaybe "" $ do
            sup <- superOf puid
            return $ "        solution__" ++ sup ++ "(k + offset__" ++ puid ++ ", indent);\n"
    
    genChildrenString :: String -> Result
    genChildrenString puid =
        concat ["        solution__" ++ cuid ++ "(k, \"    \" + indent);\n" | IClafer{uid = cuid} <- filter isNotAbstract $ childrenClaferOf puid]
    
    genRefString :: String -> Result
    genRefString puid =
        case refOf puid of
            Just "integer" ->
                "        println(\"    \" + indent + \"ref = \" + getVar(" ++ puid ++ "__ref[k]).getValue());\n"
            Just ref ->
                "        println(\"    \" + indent + \"ref = " ++ sidentOf ref ++ "\" + getVar(" ++ puid ++ "__ref[k]).getValue());\n"
            Nothing  -> ""
                
    sidentOf u = ident $ claferWithUid u
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
