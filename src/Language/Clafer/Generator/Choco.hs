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
    ++ "var scope__low__integer = -5;\n"
    ++ "var scope__high__integer = 5;\n"
    ++ "\n"
    ++ "// Offsets\n"
    ++ genOffsets
    ++ "\n"
    ++ (genConcreteClafer =<< clafers)
    ++ genAbstractClafers
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
        
    superHierarchyOf u = u : supersOf u
            
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
        
    genAbstractClafers :: Result
    genAbstractClafers =
        concat [channel sup sub | (sup, sub, _) <- subOffsets]
        where
            channel sup sub =
                "// Abstract - " ++ sup++ "/" ++ sub ++ "\n"
                ++ "for (var i = 0; i < scope__" ++ sub ++ "; i++) {\n"
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
    
    asBool True  = "true"
    asBool False = "false"

    -- Is a uniqueness constraint? If so, return the name of unique clafer
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
    
    -- Ref's as set
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
            constraint c = ["implies(member(__this, " ++ uid ++ "), " ++ genConstraintPExp c ++ ")"]
        
    nameOfType TInteger = "integer"
    nameOfType (TClafer [t]) = t
    
    namesOfType TInteger = ["integer"]
    namesOfType (TClafer ts) = ts

    genConstraintPExp :: PExp -> String
    genConstraintPExp = fst3 . genConstraintPExp'

    getCard uid =
        case card $ claferWithUid uid of
                Just (low, -1)   -> (low, scope)
                Just (low, high) -> (low, high)
        where
            scope = scopeOf uid
    getRefCard uid =
        case getCard uid of
                (0, high) -> (0, high)
                -- TODO: can tighten if has "unique" constraint somewhere in the model
                (_, high) -> (1, high)
    
    fst3 (a, _, _) = a
    (l1, h1) <*> (l2, h2) = (l1 * l2, h1 * h2)
    scopeCap scope (l, h) = (min scope l, min scope h)
    
    genConstraintPExp' :: PExp -> (String, IType, (Integer, Integer))
    -- Rearrange right joins to left joins.
    genConstraintPExp' p1@PExp{iType = Just typ, exp = IFunExp "." [p2, p3@PExp{exp = IFunExp "." [p4, p5]}]} =
        genConstraintExp typ $ IFunExp "." [p1{iType = iType p4, exp = IFunExp "." [p2, p4]}, p5]
    -- Quantifiers over various expressions are split into multiple quantifiers
    genConstraintPExp' p1@PExp{exp = IDeclPExp quant (d1 : d2 : ds) body} =
        genConstraintPExp' $ foldl buildPExp body (d1 : d2 : ds)
        where
            buildPExp body' decl' = p1{exp = IDeclPExp quant [decl'] body'}
    genConstraintPExp' PExp{iType = Just typ, exp} =
        (syntax, typ', scopeCap (sum $ map scopeOf $ namesOfType typ') size)
        where
            (syntax, typ', size) = genConstraintExp typ exp
        
    genConstraintExp :: IType -> IExp -> (String, IType, (Integer, Integer))
    -- Special constraint for references.
    -- Optimize!
    genConstraintExp typ e@(IDeclPExp quant [IDecl disj decls lbody] body) =
        case isUniqueConstraint e of
            Just sid -> (genUniqueConstraint sid, typ, (1, 1))
            Nothing  ->
                (quantFun quant ++ "(" ++ syntax ++ ", " ++ show low ++ ", " ++ show high ++ ", scope__low__" ++ nameOfType typ' ++ ", scope__high__" ++ nameOfType typ' ++ ", " ++ bodyFun ++ ", " ++ asBool disj ++ ", " ++ show (length decls) ++ ")", typ, (1, 1))
                where
                    bodyFun =
                        "function (args) { "
                            ++ concat ["var " ++ v ++" = singleton(args[" ++ show i ++ "]); " | (v, i) <- zip decls [0..]]
                            ++ "return " ++ genConstraintPExp body
                            ++ ";}"
                    v = head decls
                    (syntax, typ', (low, high)) = genConstraintPExp' lbody
                    quantFun IAll  = "allQuant"
                    quantFun ISome = "someQuant"
    genConstraintExp typ (IDeclPExp ISome [] b) =
        ("geqCard(" ++ genConstraintPExp b ++ ", 1)", typ, (1, 1))
    genConstraintExp typ (IDeclPExp INo [] b) =
        ("eqCard(" ++ genConstraintPExp b ++ ", 0)", typ, (1, 1))
    genConstraintExp typ (IFunExp "#" [arg]) =
        ("singleton(" ++ genConstraintPExp arg ++ ".getCard())", typ, (1, 1))
    genConstraintExp typ (IFunExp "=" [arg1, arg2]) =
        ("eq(" ++ genConstraintPExp arg1 ++ ", " ++ genConstraintPExp arg2 ++ ")", typ, (1, 1))
    genConstraintExp typ (IFunExp "." [arg1@PExp{iType = Just t1}, PExp{iType = Just t2, exp = IClaferId{sident = "parent"}}]) =
        ("joinParent(" ++ arg1' ++ ", scope__" ++ t1' ++ ", " ++ t1' ++ "__parent, scope__" ++ t2' ++ ")", typ, size)
        where
            t1' = nameOfType t1
            t2' = nameOfType t2
            -- TODO: size can be tighter by inspecting cardinality
            (arg1', _, size) = genConstraintPExp' arg1
    -- Optimize!
    genConstraintExp typ (IFunExp "." [PExp{iType = Just t, exp = IClaferId{sident = "this"}}, PExp{exp = IClaferId{sident = "ref"}}]) =
        ("singleton(" ++ nameOfType t ++ "__ref[__this])", typ, (1, 1))
    -- Optimize!
    genConstraintExp typ (IFunExp "." [PExp{exp = IClaferId{sident = "this"}}, PExp{exp = IClaferId{sident = child}}]) =
        ("__" ++ child ++ "[__this]", typ, (1, 1))
    genConstraintExp typ k@(IFunExp "." [arg1@PExp{iType = Just t1}, PExp{iType = Just t2, exp = IClaferId{sident = "ref"}}]) =
        ("joinRef(" ++ genConstraintPExp arg1 ++ ", scope__" ++ t1' ++ ", " ++ t1' ++ "__ref" ++ ", scope__low__" ++ t2' ++ ", scope__high__" ++ t2' ++ ")", typ, size <*> getRefCard (nameOfType t1))
        where
            t1' = nameOfType t1
            t2' = nameOfType t2
            (arg1', _, size) = genConstraintPExp' arg1
    genConstraintExp typ (IFunExp "." [arg1, PExp{exp = IClaferId{sident}}])
        | null offsets = ("joinChild(" ++ arg1' ++ ", scope__" ++ nameOfType t1 ++ ", __" ++ sident ++ ", scope__" ++ sident ++ ")", typ, size <*> getCard sident)
        | otherwise    = ("joinChild(" ++ addOffset arg1' ++ ", scope__" ++ parent ++ ", __" ++ sident ++ ", scope__" ++ sident ++ ")", typ, size <*> getCard sident)
        where
            addOffset x
                | null offsets = x
                | otherwise    = "offset(" ++ x ++ ", " ++ intercalate " + " ["offset__" ++ offset | offset <- offsets] ++ ")"
            parent = parentOf sident
            offsets = takeWhile (/= parent) $ superHierarchyOf $ nameOfType t1
            (arg1', t1, size) = genConstraintPExp' arg1
    genConstraintExp typ (IFunExp "=>" [arg1, arg2]) =
        ("implies(" ++ genConstraintPExp arg1 ++ ", " ++ genConstraintPExp arg2 ++ ")", typ, (1, 1))
    genConstraintExp typ (IFunExp "<=>" [arg1, arg2]) =
        ("ifOnlyIf(" ++ genConstraintPExp arg1 ++ ", " ++ genConstraintPExp arg2 ++ ")", typ, (1, 1))
    genConstraintExp typ (IFunExp "&&" [arg1, arg2]) =
        ("and([" ++ genConstraintPExp arg1 ++ ", " ++ genConstraintPExp arg2 ++ "])", typ, (1, 1))
    genConstraintExp typ (IFunExp "+" [arg1, arg2]) =
        ("singletonExpr(plus(" ++ genSum arg1 ++ ", " ++ genSum arg2 ++ "))", typ, (1, 1))
    genConstraintExp typ (IFunExp "-" [arg1, arg2]) =
        ("singletonExpr(minus(" ++ genSum arg1 ++ ", " ++ genSum arg2 ++ "))", typ, (1, 1))
    genConstraintExp typ (IFunExp "*" [arg1, arg2]) =
        ("singletonExpr(mult(" ++ genSum arg1 ++ ", " ++ genSum arg2 ++ "))", typ, (1, 1))
    genConstraintExp typ (IFunExp "/" [arg1, arg2]) =
        ("singletonExpr(div(" ++ genSum arg1 ++ ", " ++ genSum arg2 ++ "))", typ, (1, 1))
    genConstraintExp typ IClaferId{sident = "this"} = ("constant([__this])", typ, (1, 1))
    genConstraintExp typ IClaferId{sident} = (sident, typ, (0, scopeOf sident))
    genConstraintExp typ (IInt i) = ("constant([" ++ show i ++ "])", typ, (1, 1))
    genConstraintExp typ e = error $ "genConstraint: " ++ show e
    
    genSum pexp =
        "sumSet(" ++ syntax ++ ", " ++ show low ++ ", " ++ show high ++ ")"
        where
            (syntax, _, (low, high)) = genConstraintPExp' pexp
    

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
    scopeOf "integer" = integerScope
    scopeOf i = fromMaybe 1 $ lookup i scopes
    scopes = scopeAnalysis imodule
    
    integerScope = 20000

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