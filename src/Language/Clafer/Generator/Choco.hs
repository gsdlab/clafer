{-# LANGUAGE NamedFieldPuns #-}
{-
 Copyright (C) 2012-2017 Jimmy Liang, Michal Antkiewicz, Rafael Olaechea <http://gsd.uwaterloo.ca>

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
-- | Generates JS representation of IR for the <https://github.com/gsdlab/chocosolver Chocosolver>.
module Language.Clafer.Generator.Choco (genCModule) where

import Control.Applicative
import Control.Lens.Plated hiding (rewrite)
import Control.Monad
import Data.Data.Lens
import Data.List
import Data.Maybe
import Prelude hiding (exp)
import Language.Clafer.Common
import Language.Clafer.Intermediate.Intclafer
import Language.Clafer.Front.LexClafer


-- | A formula over the target of a reference, simplified when constant.
data Membership = MTrue | MFalse | MExp String

-- | Choco 3 code generation, with the given smallest and largest integers, if any, and the
--   number of fractional digits of decimals, if given
genCModule :: (IModule, GEnv) -> [(UID, Integer)] -> (Maybe Integer, Maybe Integer) -> Maybe Integer -> [Token] -> Result
genCModule (imodule@IModule{_mDecls}, genv') scopes  (minInt, maxInt) decimalDigits otherTokens' =
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

    genClaferNesting (IClafer{_modifiers=IClaferModifiers{_abstract=True}, _uid, _parentUID="clafer"})
        = " = Abstract(\"" ++ _uid ++ "\")"
    genClaferNesting (IClafer{_modifiers=IClaferModifiers{_abstract=True}, _uid, _parentUID})
        = " = " ++ _parentUID ++  ".addAbstractChild(\"" ++ _uid ++ "\")"
    genClaferNesting (IClafer{_modifiers=IClaferModifiers{_abstract=False}, _uid, _card, _parentUID="root"})
        = " = Clafer(\"" ++ _uid ++ "\")"
        ++ prop "withCard" (genCard _card)
    genClaferNesting (IClafer{_modifiers=IClaferModifiers{_abstract=False}, _uid, _card, _parentUID})
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
        ++ genIntRange
        ++ "stringLength(" ++ show longestString ++ ");\n"
        ++ genDecimalScale
        where
            genDecimalScale
                | usesDecimals || isJust decimalDigits = "decimalScale(" ++ show decimalScale ++ ");\n"
                | otherwise = ""
            -- Without --minint and --maxint, chocosolver chooses the range (-128..127
            -- unless overridden on its command line).
            genIntRange
                | isNothing minInt && isNothing maxInt = ""
                | otherwise = "intRange(" ++ show (fromMaybe (-128) minInt) ++ ", " ++ show (fromMaybe 127 maxInt) ++ ");\n"
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

    -- | The number of fractional digits of a decimal literal, as written, e.g., 2 for 2.50
    fractionalDigits :: String -> Integer
    fractionalDigits literal = genericLength $ drop 1 $ dropWhile (/= '.') literal

    decimalLiterals :: [String]
    decimalLiterals = [ literal | IDecimal literal <- exprs ]

    -- | Whether the model has decimal literals or references to decimals
    usesDecimals :: Bool
    usesDecimals = not (null decimalLiterals) || any refersToDecimal (universeOn biplate imodule :: [IClafer])
      where
        refersToDecimal IClafer{_reference = Just IReference{_ref = ref'}} = decimalType `elem` getRefIds ref'
        refersToDecimal _ = False

    -- | The decimal scale: the largest number of fractional digits of the decimal literals,
    --   unless given by --decimal-digits
    decimalScale :: Integer
    decimalScale = fromMaybe (maximum $ 0 : map fractionalDigits decimalLiterals) decimalDigits

    -- | A decimal literal with the fractional digits of the decimal scale, e.g., 2.5 as 2.50
    --   with 2 digits; with more digits, chocosolver reports that the literal does not fit.
    genDecimal :: String -> String
    genDecimal literal = literal ++ genericReplicate (decimalScale - fractionalDigits literal) '0'

    genSuperRefConstraintAssertGoal :: String -> IElement -> Result
    genSuperRefConstraintAssertGoal _ IEClafer{_iClafer=IClafer{_uid, _super=Nothing, _reference=Nothing, _elements}}
        = genSuperRefConstraintAssertGoal _uid =<< _elements
    genSuperRefConstraintAssertGoal _ (IEClafer c@IClafer{_uid, _card, _super, _reference, _elements})
        = _uid
        ++ prop "extending" (superOf _uid)
        ++ (case (getReference c, _reference) of
             (_, Just (IReference isSet' _ ref')) | isSetExp ref', Just target <- setExpType ref' -> refTo isSet' target
             ([target], Just (IReference isSet' _ _))                                          -> refTo isSet' target
             _                                                                                  -> "")
        ++ ";\n"
        ++ (case _reference of
             Just (IReference _ _ ref') | isSetExp ref', Just _ <- setExpType ref' -> genSetExpTarget _uid ref'
             _                                                                     -> "")
        ++ (genSuperRefConstraintAssertGoal _uid =<< _elements)
        where
            refTo True target  = ".refToUnique(" ++ genTarget target ++ ")"
            refTo False target = ".refTo(" ++ genTarget target ++ ")"
            genTarget "integer" = "Int"
            genTarget "int" = "Int"
            genTarget "decimal" = "Decimal"
            genTarget target = target
    genSuperRefConstraintAssertGoal "root" (IEConstraint True pexp) = "Constraint(" ++ genConstraintPExp pexp ++ ");\n"
    genSuperRefConstraintAssertGoal pUID (IEConstraint True pexp) = pUID ++ ".addConstraint(" ++ genConstraintPExp pexp ++ ");\n"
    genSuperRefConstraintAssertGoal _ (IEConstraint False pexp) = "assert(" ++ genConstraintPExp pexp ++ ");\n"
    genSuperRefConstraintAssertGoal _ (IEGoal True PExp{_exp=IFunExp _ [pexp]})  = "max(" ++ genConstraintPExp pexp ++ ");\n"
    genSuperRefConstraintAssertGoal _ (IEGoal False PExp{_exp=IFunExp _ [pexp]})  = "min(" ++ genConstraintPExp pexp ++ ");\n"
    genSuperRefConstraintAssertGoal _ _ = ""


    -- A reference to a set expression, e.g., `-> 1, 2, 3`, `-> integer -- 0` or
    -- `-> Alice ++ Ella`, is a reference to a type containing all its values,
    -- constrained to the values of the expression.
    isSetExp :: PExp -> Bool
    isSetExp PExp{_exp = IFunExp op' _} = op' `elem` ["++", "**", "--"]
    isSetExp _                          = False

    -- | The type to reference: the primitive type of the values, or the nearest
    -- common super of the clafers.
    setExpType :: PExp -> Maybe String
    setExpType ref' = case nub $ getRefIds ref' of
        ids@(_:_) | all isPrimitive ids -> case sort $ nub $ map normalize ids of
            [t] -> Just t
            -- integers are decimals, e.g., in `-> 1, 2.5`
            [d, i] | d == decimalType && i == integerType -> Just decimalType
            _   -> Nothing
                  | not (any isPrimitive ids) -> commonSuper ids
        _ -> Nothing
      where
        normalize "int" = "integer"
        normalize t     = t

    commonSuper :: [String] -> Maybe String
    commonSuper ids = case map supersOf ids of
        (first:rest) -> find (\u -> all (u `elem`) rest) first
        []           -> Nothing
      where
        supersOf uid' = uid' : maybe [] (tail . mapHierarchy _uid getSuper uidIClaferMap') (findIClafer uidIClaferMap' uid')

    -- | Constrains the target of the reference to the values of the set expression.
    genSetExpTarget :: String -> PExp -> String
    genSetExpTarget uid' ref'
        | Just _ <- setExpType ref', any isPrimitive (getRefIds ref') =
            case member ref' of
                MTrue    -> ""
                MFalse   -> uid' ++ ".addConstraint(none($this()));\n"
                MExp e'  -> uid' ++ ".addConstraint(" ++ e' ++ ");\n"
        | otherwise = uid' ++ ".addConstraint($in(joinRef($this()), " ++ genConstraintPExp ref' ++ "));\n"
      where
        -- membership of the target in a set expression over primitives, as a formula
        member PExp{_exp = IFunExp "++" [a, b]} = mOr (member a) (member b)
        member PExp{_exp = IFunExp "**" [a, b]} = mAnd (member a) (member b)
        member PExp{_exp = IFunExp "--" [a, b]} = mAnd (member a) (mNot $ member b)
        member PExp{_exp = IClaferId{_sident}} | isPrimitive _sident = MTrue
        member e' = MExp $ "equal(joinRef($this()), " ++ genConstraintPExp e' ++ ")"
        mOr MTrue _ = MTrue
        mOr _ MTrue = MTrue
        mOr MFalse b = b
        mOr a MFalse = a
        mOr (MExp a) (MExp b) = MExp $ "or(" ++ a ++ ", " ++ b ++ ")"
        mAnd MFalse _ = MFalse
        mAnd _ MFalse = MFalse
        mAnd MTrue b = b
        mAnd a MTrue = a
        mAnd (MExp a) (MExp b) = MExp $ "and(" ++ a ++ ", " ++ b ++ ")"
        mNot MTrue = MFalse
        mNot MFalse = MTrue
        mNot (MExp a) = MExp $ "not(" ++ a ++ ")"

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

    genConstraintExp (IFunExp "." [PExp{_exp = IClaferId{_sident = "root"}}, e2]) =
        genConstraintPExp e2
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
    genConstraintExp (IDecimal val) = "decimal(\"" ++ genDecimal val ++ "\")"
    genConstraintExp (IReal _) = error "no real numbers allowed"

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

