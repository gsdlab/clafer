{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ViewPatterns #-}

-- | Generates JS representation of IR for the <https://github.com/gsdlab/chocosolver Chocosolver>.
module Language.Clafer.Generator.Python (genPythonModule) where

import Control.Applicative
import Control.Lens.Plated hiding (rewrite)
import Control.Monad
import Data.Data.Lens
import Data.List
import Data.Maybe
import Data.Ord
import Prelude hiding (exp)
import Language.Clafer.Common
import Language.Clafer.Intermediate.Intclafer

-- | Choco 3 code generation
genPythonModule :: (IModule, GEnv) -> [(UID, Integer)] -> Result
genPythonModule (imodule@IModule{_mDecls}, genv') scopes =
    genImports
    ++ "\n"
    ++ (genAbstractClafer =<< abstractClafers)
    ++ (genConcreteClafer =<< concreteClafers)
    ++ (genRefClafer =<< clafers)
    ++ (genTopConstraint =<< _mDecls)
    ++ (genConstraint =<< clafers)
    ++ (genGoal =<< _mDecls)
    ++ genScopes
    where
    uidIClaferMap' = uidClaferMap genv'
    root :: IClafer
    root = fromJust $ findIClafer uidIClaferMap' rootIdent

    toplevelClafers = mapMaybe iclafer _mDecls
    -- The sort is so that we encounter sub clafers before super clafers when abstract clafers extend other abstract clafers
    abstractClafers = sortBy (comparing $ length . supersOf . _uid) $ filter _isAbstract toplevelClafers
    parentChildMap = childClafers root
    clafers = snd <$> parentChildMap
    claferUids = _uid <$> clafers
    concreteClafers = filter isNotAbstract clafers

    claferWithUid u = fromMaybe (error $ "claferWithUid: \"" ++ u ++ "\" is not a clafer") $ findIClafer uidIClaferMap' u

    -- All abstract clafers u inherits
    supersOf :: String -> [String]
    supersOf u =
        case superOf u of
             Just su -> su : supersOf su
             Nothing -> []

    superOf u =
        case _super $ claferWithUid u of
            Just (PExp{_exp = IClaferId{_sident}})
                | _sident == baseClafer -> Nothing
                | isPrimitive _sident   -> Nothing
                | otherwise             -> Just _sident
            _ -> Nothing

{-    refOf u =
        case _reference $ claferWithUid u of
            Just (IReference{_ref=PExp{_exp = IClaferId{_sident}}})
                | _sident == "int"    -> Just "integer"
                | isPrimitive _sident -> Just _sident
                | otherwise           -> Nothing
            _ -> Nothing
-}
    parentOf u = fst $ fromMaybe (error $ "parentOf: \"" ++ u ++ "\" is not a clafer") $ find ((== u) . _uid . snd) parentChildMap

    genCard :: Interval -> Maybe String
    genCard (0, -1) = Nothing
    genCard (low, -1) = return $ show low
    genCard (low, high) = return $ show low ++ ", " ++ show high

    genImports = concat
      [ "from jsir.IR import *\n"

      ]

    genScopes :: Result
    genScopes =
        (if null scopeMap then "" else "scope({" ++ intercalate ", " scopeMap ++ "});\n")
        ++ "defaultScope(1);\n"
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
    genConcreteClafer (IClafer _ _ (Just (IGCard _ _)) _ _ _ _ _ Nothing _ _) = error "Choco.getConcreteClafer undefined"

    prop name value =
        case value of
                Just value' -> "." ++ name ++ "(" ++ value' ++ ")"
                Nothing     -> ""


    genRefClafer :: IClafer -> Result
    genRefClafer c@IClafer{_uid, _reference, _card} =
        case (getReference c, _reference, _card) of
             ([target], Just (IReference True _), Just (lb, ub))  -> if (lb > 1 || ub > 1 || lb == -1 || ub == -1)
                then _uid ++ ".refToUnique(" ++ genTarget target ++ ");\n"
                else _uid ++ ".refTo(" ++ genTarget target ++ ");\n"
             ([target], Just (IReference _ _), _) -> _uid ++ ".refTo(" ++ genTarget target ++ ");\n"
             _ -> ""
        where
            genTarget "integer" = "\"int\""
            genTarget "int" = "\"int\""
            genTarget target = target

    genAbstractClafer :: IClafer -> Result
    genAbstractClafer IClafer{_uid, _card = Just _} =
        _uid ++ " = Abstract(\"" ++ _uid ++ "\")" ++ prop "extending" (superOf _uid) ++ ";\n"
    genAbstractClafer IClafer{_uid, _card = Nothing} =
        _uid ++ " = Abstract(\"" ++ _uid ++ "\")" ++ prop "extending" (superOf _uid) ++ ";\n"


    genTopConstraint :: IElement -> Result
    genTopConstraint (IEConstraint _ pexp) = "Constraint(" ++ genConstraintPExp pexp ++ ");\n"
    genTopConstraint _ = ""

    genConstraint :: IClafer -> Result
    genConstraint IClafer{_uid, _elements} =
        unlines [_uid ++ ".addConstraint(" ++ genConstraintPExp c ++ ");"
            | c <- mapMaybe iconstraint _elements]

    genGoal :: IElement -> Result
    genGoal (IEGoal _ PExp{_exp = IFunExp{_op="max", _exps=[expr]}})  = "max(" ++ genConstraintPExp expr ++ ");\n"
    genGoal (IEGoal _ PExp{_exp = IFunExp{_op="min", _exps=[expr]}})  = "min(" ++ genConstraintPExp expr ++ ");\n"
    genGoal (IEGoal _ _) = error $ "Unknown objective"
    genGoal _ = ""

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
        | otherwise = error "Python: Unexpected sum argument."
    genConstraintExp (IFunExp "product" args')
        | [arg] <- args', PExp{_exp = IFunExp{_exps = [a, PExp{_exp = IClaferId{_sident = "ref"}}]}} <- rewrite arg =
            "product(" ++ genConstraintPExp a ++ ")"
        | otherwise = error "Python: Unexpected product argument."
    genConstraintExp (IFunExp "+" args') =
        (if _iType (head args') == Just TString then "concat" else "add") ++
            "(" ++ intercalate ", " (map genConstraintPExp args') ++ ")"
    genConstraintExp (IFunExp op' args') =
        mapFunc op' ++ "(" ++ intercalate ", " (map genConstraintPExp args') ++ ")"
    -- this is a keyword in Javascript so use "$this" instead
    genConstraintExp IClaferId{_sident = "this"} = "$this()"
    genConstraintExp IClaferId{_sident}
        | _sident `elem` claferUids = "glob(" ++ _sident ++ ")"
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
    mapFunc "in" = "set_in"
    mapFunc "not in" = "set_nin"
    mapFunc "+" = "add"
    mapFunc "*" = "mul"
    mapFunc "/" = "div"
    mapFunc "%" = "mod"
    mapFunc "++" = "set_union"
    mapFunc "--" = "set_diff"
    mapFunc "**" = "set_inter"
    mapFunc "ifthenelse" = "ifThenElse"
    mapFunc op' = error $ "Python: Unknown op: " ++ op'

{-    sidentOf u = ident $ claferWithUid u
    scopeOf "integer" = undefined
    scopeOf "int" = undefined
    scopeOf i = fromMaybe 1 $ lookup i scopes
    bitwidth = fromMaybe 4 $ lookup "int" scopes :: Integer  -}

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
