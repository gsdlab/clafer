{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ViewPatterns #-}

-- | Generates JS representation of IR for the <https://github.com/gsdlab/chocosolver Chocosolver>.
module Language.Clafer.Generator.Choco (genCModule) where

import Control.Applicative
import Control.Lens.Plated hiding (rewrite)
import Control.Monad
import Data.Data.Lens
import Data.List
import Data.Maybe
import Data.Ord
import Prelude hiding (exp)
import Language.Clafer.ClaferArgs
import Language.Clafer.Common
import Language.Clafer.Front.Absclafer
import Language.Clafer.Intermediate.Intclafer

-- | Choco 3 code generation
genCModule :: ClaferArgs -> (IModule, GEnv) -> [(UID, Integer)] -> Result
genCModule _ (imodule@IModule{_mDecls}, _) scopes =
    genScopes
    ++ "\n"
    ++ (genAbstractClafer =<< abstractClafers)
    ++ (genConcreteClafer =<< concreteClafers)
    ++ (genRefClafer =<< clafers)
    ++ (genTopConstraint =<< _mDecls)
    ++ (genConstraint =<< clafers)
    ++ (genGoal =<< _mDecls)
    where
    root :: IClafer
    root = IClafer noSpan False Nothing rootIdent rootIdent "" (ISuper False [PExp Nothing "" noSpan $ IClaferId "" baseClafer True Nothing]) (Just (1, 1)) (0, 0) True _mDecls
    toplevelClafers = mapMaybe iclafer _mDecls
    -- The sort is so that we encounter sub clafers before super clafers when abstract clafers extend other abstract clafers
    abstractClafers = sortBy (comparing $ length . supersOf . _uid) $ filter _isAbstract toplevelClafers
    parentChildMap = childClafers root
    clafers = snd <$> parentChildMap
    claferUids = _uid <$> clafers
    concreteClafers = filter isNotAbstract clafers
--    minusRoot = filter ((/= "root") . uid)

    claferWithUid u = fromMaybe (error $ "claferWithUid: \"" ++ u ++ "\" is not a clafer") $ find ((== u) . _uid) clafers

    -- All abstract clafers u inherits
    supersOf :: String -> [String]
    supersOf u =
        case superOf u of
             Just su -> su : supersOf su
             Nothing -> []

--    superHierarchyOf u = u : supersOf u

    superOf u =
        case _super $ claferWithUid u of
            ISuper False [PExp{_exp = IClaferId{_sident}}]
                | _sident == baseClafer -> Nothing
                | isPrimitive _sident   -> Nothing
                | otherwise             -> Just _sident
            _ -> Nothing

{-    superWithRef u =
        case mapMaybe refOf $ supersOf u of
             r : _ -> r
             _      -> u ++ " does not inherit a ref" -}

    refOf u =
        case _super $ claferWithUid u of
            ISuper True [PExp{_exp = IClaferId{_sident}}] -> Just _sident
            ISuper False [PExp{_exp = IClaferId{_sident}}]
                | _sident == "int"    -> Just "integer"
                | isPrimitive _sident -> Just _sident
                | otherwise           -> Nothing
            _ -> Nothing

    -- All clafers that inherit u
{-    subOf :: String -> [String]
    subOf u = [uid | IClafer{_uid} <- clafers, Just u == superOf uid]
    subClaferOf :: String -> [IClafer]
    subClaferOf = map claferWithUid . subOf

    subOffsets :: [(String, String, Integer)]
    subOffsets = [(uid, sub, off) | IClafer{_uid} <- clafers, let subs = subOf uid, (sub, off) <- zip subs $ offsets subs]

    subOffsetOf :: String -> Integer
    subOffsetOf sub = trd3 $ fromMaybe (error $ "subOffsetOf: " ++ sub) $ find ((== sub) . snd3) subOffsets

    offsets :: [String] -> [Integer]
    offsets = scanl (flip $ (+) . scopeOf) 0
-}

    parentOf u = fst $ fromMaybe (error $ "parentOf: \"" ++ u ++ "\" is not a clafer") $ find ((== u) . _uid . snd) parentChildMap
{-    parentClaferOf = claferWithUid . parentOf
    -- Direct childrens
    childrenOf = map uid . childrenClaferOf
    childrenClaferOf u = [c | (p, c) <- parentChildMap, p == u]

    -- Indirect childrens
    indirectChildrenOf u = childrenOf =<< supersOf u
    indirectChildrenClaferOf u = childrenClaferOf =<< supersOf u

    isBounded :: Interval -> Bool
    isBounded (0, -1) = False
    isBounded _       = True
-}
    genCard :: Interval -> Maybe String
    genCard (0, -1) = Nothing
    genCard (low, -1) = return $ show low
    genCard (low, high) = return $ show low ++ ", " ++ show high


    genScopes :: Result
    genScopes =
        (if null scopeMap then "" else "scope({" ++ intercalate ", " scopeMap ++ "});\n")
        ++ "defaultScope(1);\n"
        ++ "intRange(-" ++ show (2 ^ (bitwidth - 1)) ++ ", " ++ show (2 ^ (bitwidth - 1) - 1) ++ ");\n"
        ++ "stringLength(" ++ show longestString ++ ");\n"
        where
            scopeMap = [uid' ++ ":" ++ show scope | (uid', scope) <- scopes, uid' /= "int"]
    exprs :: [IExp]
    exprs = universeOn biplate imodule

    stringLength :: IExp -> Maybe Int
    stringLength (IStr string) = Just $ length string
    stringLength _ = Nothing

    longestString :: Int
    longestString = maximum $ 16 : mapMaybe stringLength exprs

    genConcreteClafer :: IClafer -> Result
    genConcreteClafer IClafer{_uid, _card = Just _card, _gcard = Just (IGCard _ _gcard)} =
            _uid ++ " = " ++ constructor ++ "(\"" ++ _uid ++ "\")" ++ prop "withCard" (genCard _card) ++ prop "withGroupCard" (genCard _gcard) ++ prop "extending" (superOf _uid) ++ ";\n"
        where
            constructor =
                case parentOf _uid of
                     "root" -> "Clafer"
                     puid   -> puid ++ ".addChild"
    genConcreteClafer (IClafer _ _ Nothing _ _ _ _ _ _ _ _) = error "Choco.getConcreteClafer undefined"
    genConcreteClafer (IClafer _ _ (Just (IGCard _ _)) _ _ _ _ Nothing _ _ _) = error "Choco.getConcreteClafer undefined"

    prop name value =
        case value of
                Just value' -> "." ++ name ++ "(" ++ value' ++ ")"
                Nothing     -> ""


    genRefClafer :: IClafer -> Result
    genRefClafer IClafer{_uid} =
        case (refOf _uid, _uid `elem` uniqueRefs) of
             (Just target, True)  -> _uid ++ ".refToUnique(" ++ genTarget target ++ ");\n"
             (Just target, False) -> _uid ++ ".refTo(" ++ genTarget target ++ ");\n"
             _                    -> ""
        where
            genTarget "integer" = "Int"
            genTarget target = target

    genAbstractClafer :: IClafer -> Result
    genAbstractClafer IClafer{_uid, _card = Just _} =
        _uid ++ " = Abstract(\"" ++ _uid ++ "\")" ++ prop "extending" (superOf _uid) ++ ";\n"
    genAbstractClafer IClafer{_uid, _card = Nothing} =
        _uid ++ " = Abstract(\"" ++ _uid ++ "\")" ++ prop "extending" (superOf _uid) ++ ";\n"

    -- Is a uniqueness constraint? If so, return the name of unique clafer
    isUniqueConstraint :: IExp -> Maybe String
    isUniqueConstraint (IDeclPExp IAll [IDecl True [x, y] PExp{_exp = IClaferId{_sident}}]
        PExp{_exp = IFunExp "!=" [
            PExp{_exp = IFunExp "." [PExp{_exp = IClaferId{_sident = xident}}, PExp{_exp = IClaferId{_sident = "ref"}}]},
            PExp{_exp = IFunExp "." [PExp{_exp = IClaferId{_sident = yident}}, PExp{_exp = IClaferId{_sident = "ref"}}]}]})
                | x == xident && y == yident = return _sident
                | otherwise                  = mzero
    isUniqueConstraint  (IDeclPExp IAll [IDecl True [x, y] PExp{_exp = IFunExp "." [PExp{_exp = IClaferId{_sident = "this"}}, PExp{_exp = IClaferId{_sident}}]}]
        PExp{_exp = IFunExp "!=" [
            PExp{_exp = IFunExp "." [PExp{_exp = IClaferId{_sident = xident}}, PExp{_exp = IClaferId{_sident = "ref"}}]},
            PExp{_exp = IFunExp "." [PExp{_exp = IClaferId{_sident = yident}}, PExp{_exp = IClaferId{_sident = "ref"}}]}]})
                | x == xident && y == yident = return _sident
                | otherwise                  = mzero
    isUniqueConstraint _ = mzero

    uniqueRefs :: [String]
    uniqueRefs = mapMaybe isUniqueConstraint $ map _exp $ mapMaybe iconstraint $ _mDecls ++ (clafers >>= _elements)

    genTopConstraint :: IElement -> Result
    genTopConstraint (IEConstraint _ pexp)
        | isNothing $ isUniqueConstraint $ _exp pexp = "Constraint(" ++ genConstraintPExp pexp ++ ");\n"
        | otherwise                                 = ""
    genTopConstraint _ = ""

    genConstraint :: IClafer -> Result
    genConstraint IClafer{_uid, _elements} =
        unlines [_uid ++ ".addConstraint(" ++ genConstraintPExp c ++ ");"
            | c <- filter (isNothing . isUniqueConstraint . _exp) $ mapMaybe iconstraint _elements]

    genGoal :: IElement -> Result
    genGoal (IEGoal _ PExp{_exp = IFunExp{_op="max", _exps=[expr]}})  = "max(" ++ genConstraintPExp expr ++ ");\n"
    genGoal (IEGoal _ PExp{_exp = IFunExp{_op="min", _exps=[expr]}})  = "min(" ++ genConstraintPExp expr ++ ");\n"
    genGoal (IEGoal _ _) = error $ "Unknown objective"
    genGoal _ = ""

{-    nameOfType TInteger = "integer"
    nameOfType (TClafer [t]) = t

    namesOfType TInteger = ["integer"]
    namesOfType (TClafer ts) = ts

    getCard uid =
        case card $ claferWithUid uid of
                Just (low, -1)   -> (low, scope)
                Just (low, high) -> (low, high)
        where
            scope = scopeOf uid

    (l1, h1) <*> (l2, h2) = (l1 * l2, h1 * h2)
    scopeCap scope (l, h) = (min scope l, min scope h)
-}
    rewrite :: PExp -> PExp
    -- Rearrange right joins to left joins.
    rewrite p1@PExp{_iType = Just _, _exp = IFunExp "." [p2, p3@PExp{_exp = IFunExp "." _}]} =
        p1{_exp = IFunExp "." [p3{_iType = _iType p4, _exp = IFunExp "." [p2, p4]}, p5]}
        where
            PExp{_exp = IFunExp "." [p4, p5]} = rewrite p3
    rewrite p1@PExp{_exp = IFunExp{_op = "-", _exps = [PExp{_exp = IInt i}]}} =
        -- This is so that the output looks cleaner, no other purpose since the Choco optimizer
        -- in the backend will treat the pre-rewritten expression the same.
        p1{_exp = IInt (-i)}
    rewrite p = p

    genConstraintPExp :: PExp -> String
    genConstraintPExp = genConstraintExp . _exp . rewrite

    genConstraintExp :: IExp -> String
    genConstraintExp (IDeclPExp quant' [] body') =
        mapQuant quant' ++ "(" ++ genConstraintPExp body' ++ ")"
    genConstraintExp (IDeclPExp quant' decls' body') =
        mapQuant quant' ++ "([" ++ intercalate ", " (map genDecl decls') ++ "], " ++ genConstraintPExp body' ++ ")"
        where
            genDecl (IDecl isDisj' locals body'') =
                (if isDisj' then "disjDecl" else "decl") ++ "([" ++ intercalate ", " (map genLocal locals) ++ "], " ++ genConstraintPExp body'' ++ ")"
            genLocal local =
                local ++ " = local(\"" ++ local ++ "\")"

    genConstraintExp (IFunExp "." [e1, PExp{_exp = IClaferId{_sident = "ref"}}]) =
        "joinRef(" ++ genConstraintPExp e1 ++ ")"
    genConstraintExp (IFunExp "." [e1, PExp{_exp = IClaferId{_sident = "parent"}}]) =
        "joinParent(" ++ genConstraintPExp e1 ++ ")"
    genConstraintExp (IFunExp "." [e1, PExp{_exp = IClaferId{_sident}}]) =
        "join(" ++ genConstraintPExp e1 ++ ", " ++ _sident ++ ")"
    genConstraintExp (IFunExp "." [_, _]) =
        error $ "Did not rewrite all joins to left joins."
    genConstraintExp (IFunExp "-" [arg]) =
        "minus(" ++ genConstraintPExp arg ++ ")"
    genConstraintExp (IFunExp "-" [arg1, arg2]) =
        "sub(" ++ genConstraintPExp arg1 ++ ", " ++ genConstraintPExp arg2 ++ ")"
    genConstraintExp (IFunExp "sum" args')
        | [arg] <- args', PExp{_exp = IFunExp{_exps = [a, PExp{_exp = IClaferId{_sident = "ref"}}]}} <- rewrite arg =
            "sum(" ++ genConstraintPExp a ++ ")"
        | otherwise = error "Choco: Unexpected sum argument."
    genConstraintExp (IFunExp "+" args') =
	(if _iType (head args') == Just TString then "concat" else "add") ++
            "(" ++ intercalate ", " (map genConstraintPExp args') ++ ")"
    genConstraintExp (IFunExp op' args') =
        mapFunc op' ++ "(" ++ intercalate ", " (map genConstraintPExp args') ++ ")"
    -- this is a keyword in Javascript so use "$this" instead
    genConstraintExp IClaferId{_sident = "this"} = "$this()"
    genConstraintExp IClaferId{_sident}
        | _sident `elem` claferUids = "global(" ++ _sident ++ ")"
        | otherwise                = _sident
    genConstraintExp (IInt val) = "constant(" ++ show val ++ ")"
    genConstraintExp (IStr val) = "constant(" ++ show val ++ ")"
    genConstraintExp (IDouble val) = "constant(" ++ show val ++ ")"

    mapQuant INo = "none"
    mapQuant ISome = "some"
    mapQuant IAll = "all"
    mapQuant IOne = "one"
    mapQuant ILone = "lone"

    mapFunc "!" = "not"
    mapFunc "#" = "card"
    mapFunc "<=>" = "ifOnlyIf"
    mapFunc "=>" = "implies"
    mapFunc "||" = "or"
    mapFunc "xor" = "xor"
    mapFunc "&&" = "and"
    mapFunc "<" = "lessThan"
    mapFunc ">" = "greaterThan"
    mapFunc "=" = "equal"
    mapFunc "<=" = "lessThanEqual"
    mapFunc ">=" = "greaterThanEqual"
    mapFunc "!=" = "notEqual"
    mapFunc "in" = "$in"
    mapFunc "not in" = "notIn"
    mapFunc "+" = "add"
    mapFunc "*" = "mul"
    mapFunc "/" = "div"
    mapFunc "++" = "union"
    mapFunc "--" = "diff"
    mapFunc "&" = "inter"
    mapFunc "ifthenelse" = "ifThenElse"
    mapFunc op' = error $ "Choco: Unknown op: " ++ op'

{-    sidentOf u = ident $ claferWithUid u
    scopeOf "integer" = undefined
    scopeOf "int" = undefined
    scopeOf i = fromMaybe 1 $ lookup i scopes -}
    bitwidth = fromMaybe 4 $ lookup "int" scopes :: Integer

-- isQuant PExp{_exp = IDeclPExp{}} = True
-- isQuant _ = False

isNotAbstract :: IClafer -> Bool
isNotAbstract = not . _isAbstract

iclafer :: IElement -> Maybe IClafer
iclafer (IEClafer c) = Just c
iclafer _ = Nothing

iconstraint :: IElement -> Maybe PExp
iconstraint (IEConstraint _ pexp) = Just pexp
iconstraint _ = Nothing

childClafers :: IClafer -> [(String, IClafer)]
childClafers IClafer{_uid, _elements} =
    childClafers' _uid =<< mapMaybe iclafer _elements
    where
    childClafers' parent' c@IClafer{_uid, _elements} = (parent', c) : (childClafers' _uid  =<< mapMaybe iclafer _elements)
