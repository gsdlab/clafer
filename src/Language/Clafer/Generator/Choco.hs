{-# LANGUAGE NamedFieldPuns #-}

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
import Language.Clafer.Common
import Language.Clafer.Intermediate.Intclafer
import Language.Clafer.Front.LexClafer


-- | Choco 3 code generation
genCModule :: (IModule, GEnv) -> [(UID, Integer)] -> [Token]     -> Result
genCModule (imodule@IModule{_mDecls}, genv') scopes  otherTokens' =
    genScopes
    ++ "\n"
    ++ (genClafers =<< _mDecls)
    ++ (genSuperRefConstraintAssertGoal "root" =<< _mDecls)
    ++ genChocoEscapes
    where
    uidIClaferMap' = uidClaferMap genv'

    genClafers :: IElement -> String
    genClafers    (IEClafer (c@IClafer{_uid, _gcard, _elements}))
        = _uid
        ++ genClaferNesting c
        ++ prop "withGroupCard" (genCard $ _interval <$> _gcard)
        ++ ";\n"
        ++ (genClafers =<< _elements)
    genClafers    _ = ""

    genClaferNesting (IClafer{_isAbstract=True, _uid, _parentUID="clafer"})
        = " = Abstract(\"" ++ _uid ++ "\")"
    genClaferNesting (IClafer{_isAbstract=True, _uid, _parentUID})
        = " = " ++ _parentUID ++  ".addAbstractChild(\"" ++ _uid ++ "\")"
    genClaferNesting (IClafer{_isAbstract=False, _uid, _card, _parentUID="root"})
        = " = Clafer(\"" ++ _uid ++ "\")"
        ++ prop "withCard" (genCard _card)
    genClaferNesting (IClafer{_isAbstract=False, _uid, _card, _parentUID})
        = " = "
        ++ _parentUID
        ++  ".addChild(\"" ++ _uid ++ "\")"
        ++ prop "withCard" (genCard _card)

    prop name value =
        case value of
                Just value' -> "." ++ name ++ "(" ++ value' ++ ")"
                Nothing     -> ""

    claferWithUid u = fromMaybe (error $ "claferWithUid: \"" ++ u ++ "\" is not a clafer") $ findIClafer uidIClaferMap' u

    superOf u =
        case _super $ claferWithUid u of
            Just (PExp{_exp = IClaferId{_sident}})
                | _sident == baseClafer -> Nothing
                | isPrimitive _sident   -> Nothing
                | otherwise             -> Just _sident
            _ -> Nothing

    genCard :: Maybe Interval -> Maybe String
    genCard (Just (0, -1)) = Nothing
    genCard (Just (low, -1)) = return $ show low
    genCard (Just (low, high)) = return $ show low ++ ", " ++ show high
    genCard _              = Nothing


    genScopes :: Result
    genScopes =
        (if null scopeMap then "" else "scope({" ++ intercalate ", " scopeMap ++ "});\n")
        ++ "defaultScope(1);\n"
        ++ "intRange(-" ++ show largestPositiveInt ++ ", " ++ show (largestPositiveInt - 1) ++ ");\n"
        ++ "stringLength(" ++ show longestString ++ ");\n"
        where
            largestPositiveInt :: Integer
            largestPositiveInt = 2 ^ (bitwidth - 1)
            scopeMap = [uid' ++ ":" ++ show scope | (uid', scope) <- scopes, uid' /= "int"]

    genChocoEscapes :: String
    genChocoEscapes = concatMap printChocoEscape otherTokens'
        where
            printChocoEscape (PT _ (T_PosChoco code)) =  let
                code' = fromJust $ stripPrefix "[choco|" code
              in
                take (length code' - 2) code'
            printChocoEscape _                        = ""

    exprs :: [IExp]
    exprs = universeOn biplate imodule

    stringLength :: IExp -> Maybe Int
    stringLength (IStr string) = Just $ length string
    stringLength _ = Nothing

    longestString :: Int
    longestString = maximum $ 16 : mapMaybe stringLength exprs

    genSuperRefConstraintAssertGoal :: String -> IElement -> Result
    genSuperRefConstraintAssertGoal _ IEClafer{_iClafer=IClafer{_uid, _super=Nothing, _reference=Nothing, _elements}}
        = genSuperRefConstraintAssertGoal _uid =<< _elements
    genSuperRefConstraintAssertGoal _ (IEClafer c@IClafer{_uid, _card, _super, _reference, _elements})
        = _uid
        ++ prop "extending" (superOf _uid)
        ++ (case (getReference c, _reference, _card) of
             ([target], Just (IReference True _), Just (lb, ub))  -> if lb > 1 || ub > 1 || lb == -1 || ub == -1
                then ".refToUnique(" ++ genTarget target ++ ")"
                else ".refTo(" ++ genTarget target ++ ")"
             ([target], Just (IReference _ _), _) -> ".refTo(" ++ genTarget target ++ ")"
             _ -> "")
        ++ ";\n"
        ++ (genSuperRefConstraintAssertGoal _uid =<< _elements)
        where
            genTarget "integer" = "Int"
            genTarget "int" = "Int"
            genTarget target = target
    genSuperRefConstraintAssertGoal "root" (IEConstraint True pexp) = "Constraint(" ++ genConstraintPExp pexp ++ ");\n"
    genSuperRefConstraintAssertGoal pUID (IEConstraint True pexp) = pUID ++ ".addConstraint(" ++ genConstraintPExp pexp ++ ");\n"
    genSuperRefConstraintAssertGoal _ (IEConstraint False pexp) = "assert(" ++ genConstraintPExp pexp ++ ");\n"
    genSuperRefConstraintAssertGoal _ (IEGoal True PExp{_exp=IFunExp _ [pexp]})  = "max(" ++ genConstraintPExp pexp ++ ");\n"
    genSuperRefConstraintAssertGoal _ (IEGoal False PExp{_exp=IFunExp _ [pexp]})  = "min(" ++ genConstraintPExp pexp ++ ");\n"
    genSuperRefConstraintAssertGoal _ _ = ""


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

    genConstraintExp (IFunExp "." [e1, PExp{_exp = IClaferId{_sident = "dref"}}]) =
        "joinRef(" ++ genConstraintPExp e1 ++ ")"
    genConstraintExp (IFunExp "." [e1, PExp{_exp = IClaferId{_sident = "parent"}}]) =
        "joinParent(" ++ genConstraintPExp e1 ++ ")"
    genConstraintExp (IFunExp "." [e1, PExp{_exp = IClaferId{_sident}}]) =
        "join(" ++ genConstraintPExp e1 ++ ", " ++ _sident ++ ")"
    genConstraintExp (IFunExp "." [_, _]) =
        error "Did not rewrite all joins to left joins."
    genConstraintExp (IFunExp "-" [arg]) =
        "minus(" ++ genConstraintPExp arg ++ ")"
    genConstraintExp (IFunExp "-" [arg1, arg2]) =
        "sub(" ++ genConstraintPExp arg1 ++ ", " ++ genConstraintPExp arg2 ++ ")"
    genConstraintExp (IFunExp "sum" args')
        | [arg] <- args', PExp{_exp = IFunExp{_exps = [a, PExp{_exp = IClaferId{_sident = "dref"}}]}} <- rewrite arg =
            "sum(" ++ genConstraintPExp a ++ ")"
        | [arg] <- args' =
            "sum(" ++ genConstraintPExp arg ++ ")"
        | otherwise = error $ "[bug] Choco.genConstraintExp: Unexpected sum argument: " ++ show args'
    genConstraintExp (IFunExp "product" args')
        | [arg] <- args', PExp{_exp = IFunExp{_exps = [a, PExp{_exp = IClaferId{_sident = "dref"}}]}} <- rewrite arg =
            "product(" ++ genConstraintPExp a ++ ")"
        | otherwise = error "Choco: Unexpected product argument."
    genConstraintExp (IFunExp "+" args') =
        (if _iType (head args') == Just TString then "concat" else "add") ++
            "(" ++ intercalate ", " (map genConstraintPExp args') ++ ")"
    genConstraintExp (IFunExp op' args') =
        mapFunc op' ++ "(" ++ intercalate ", " (map genConstraintPExp args') ++ ")"
    -- this is a keyword in Javascript so use "$this" instead
    genConstraintExp IClaferId{_sident = "this"} = "$this()"
    genConstraintExp IClaferId{_sident}
        | isJust $ findIClafer uidIClaferMap' _sident = "global(" ++ _sident ++ ")"
        | otherwise                = _sident
    genConstraintExp (IInt val) = "constant(" ++ show val ++ ")"
    genConstraintExp (IStr val) = "constant(" ++ show val ++ ")"
    genConstraintExp (IDouble val) = "constant(" ++ show val ++ ")"
    genConstraintExp (IReal val) = "constant(" ++ show val ++ ")"

    mapQuant INo = "none"
    mapQuant ISome = "some"
    mapQuant IAll = "all"
    mapQuant IOne = "one"
    mapQuant ILone = "lone"

    mapFunc "!" = "not"
    mapFunc "#" = "card"
    mapFunc "min" = "minimum"
    mapFunc "max" = "maximum"
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
    mapFunc "%" = "mod"
    mapFunc "++" = "union"
    mapFunc "--" = "diff"
    mapFunc "**" = "inter"
    mapFunc "ifthenelse" = "ifThenElse"
    mapFunc op' = error $ "Choco: Unknown op: " ++ op'

    bitwidth = fromMaybe 4 $ lookup "int" scopes :: Integer
