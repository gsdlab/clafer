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
-- | The model the <https://github.com/gsdlab/chocosolver Chocosolver> solves, built by one walk
--   over the IR, which "Language.Clafer.Generator.Choco" prints as JavaScript and
--   "Language.Clafer.Generator.Explicit" as an explicit Clafer model, so that both give the same
--   model.
module Language.Clafer.Generator.ChocoModel
  ( CModel(..)
  , CElement(..)
  , CClafer(..)
  , CExp(..)
  , CDecl(..)
  , CScope(..)
  , chocoModel
  ) where

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
data Membership = MTrue | MFalse | MExp CExp

-- | The model chocosolver gets: its clafers and the elements in them, in the order of the IR.
data CModel = CModel
    { cmElements :: [CElement]    -- ^ the top-level clafers, constraints, objectives and assertions
    , cmScope    :: CScope
    , cmEscapes  :: String        -- ^ the [choco| |] escapes, JavaScript
    }

data CElement
    = CEClafer CClafer
    | CEConstraint CExp
    | CEAssert CExp               -- ^ an assertion, quantified over its clafer if nested
    | CEObjective Bool CExp       -- ^ maximize, or minimize

data CClafer = CClafer
    { ccUid      :: UID
    , ccParent   :: UID           -- ^ "clafer" for a top-level abstract clafer, "root" for a top-level concrete one
    , ccAbstract :: Bool
    , ccModifiers :: [String]     -- ^ its temporal modifiers, e.g., initial, final, finalref, which chocosolver does not read
    , ccCard     :: Maybe Interval   -- ^ only if not 0..*
    , ccGCard    :: Maybe Interval   -- ^ only if not 0..*
    , ccLinked   :: Bool          -- ^ whether it has a super clafer or a reference in the IR
    , ccSuper    :: Maybe UID     -- ^ a clafer
    , ccRef      :: Maybe (Bool, String)   -- ^ its own reference: whether a set, and the target
    , ccRefConstraints :: [CExp]  -- ^ the constraints of a reference to a set expression
    , ccElements :: [CElement]
    }

-- | An expression, by the functions of chocosolver's JavaScript API.
data CExp
    = CThis
    | CGlobal UID                 -- ^ all instances of a clafer
    | CName String                -- ^ a local
    | CInt Integer
    | CStr String                 -- ^ a Clafer string literal, with its quotes
    | CDouble Double
    | CDecimal String             -- ^ as written, with the fractional digits of the decimal scale
    | CEmpty String               -- ^ the empty set, typed by a clafer (or Int)
    | CJoin CExp String
    | CJoinRef CExp
    | CJoinParent CExp
    | CFun String [CExp]          -- ^ a function of the API by its name, e.g., equal
    | CQuant IQuant [CDecl] CExp  -- ^ without declarations, a quantifier over a set, e.g., none(x)

data CDecl = CDecl Bool [String] CExp

-- | The scopes, as chocosolver solves the model with no options.
data CScope = CScope
    { csClafers       :: [(UID, Integer)]   -- ^ the scopes given, without int
    , csIntRange      :: Maybe (Integer, Integer)
    , csStringLength  :: Int
    , csDecimalScale  :: Maybe Integer      -- ^ only if the model uses decimals or the scale is given
    }

-- | The model of the IR, with the given scopes, smallest and largest integers, if any, number of
--   fractional digits of decimals, if given, and the tokens with the [choco| |] escapes
chocoModel :: (IModule, GEnv) -> [(UID, Integer)] -> (Maybe Integer, Maybe Integer) -> Maybe Integer -> [Token] -> CModel
chocoModel (imodule@IModule{_mDecls}, genv') scopes (minInt, maxInt) decimalDigits otherTokens' =
    CModel
    { cmElements = mapMaybe (genElement "root") _mDecls
    , cmScope = CScope
        { csClafers = [(uid', scope) | (uid', scope) <- scopes, uid' /= "int"]
        -- Without --minint and --maxint, chocosolver chooses the range (-128..127
        -- unless overridden on its command line).
        , csIntRange = if isNothing minInt && isNothing maxInt then Nothing
                       else Just (fromMaybe (-128) minInt, fromMaybe 127 maxInt)
        , csStringLength = longestString
        , csDecimalScale = if usesDecimals || isJust decimalDigits then Just decimalScale else Nothing
        }
    , cmEscapes = genChocoEscapes
    }
    where
    uidIClaferMap' = uidClaferMap genv'

    genElement :: String -> IElement -> Maybe CElement
    genElement _ (IEClafer c@IClafer{_uid, _card, _gcard, _super, _reference, _elements, _parentUID, _modifiers}) = Just $ CEClafer CClafer
        { ccUid = _uid
        , ccParent = _parentUID
        , ccAbstract = _abstract _modifiers
        , ccModifiers = temporalModifiers' _modifiers _reference
        , ccCard = nonDefault _card
        , ccGCard = nonDefault $ _interval <$> _gcard
        , ccLinked = isJust _super || isJust _reference
        , ccSuper = superOf _uid
        , ccRef = case (getReference c, _reference) of
             (_, Just (IReference isSet' _ ref')) | isSetExp ref', Just target <- setExpType ref' -> Just (isSet', target)
             ([target], Just (IReference isSet' _ _))                                          -> Just (isSet', target)
             _                                                                                  -> Nothing
        , ccRefConstraints = case _reference of
             Just (IReference _ _ ref') | isSetExp ref', Just _ <- setExpType ref' -> genSetExpTarget ref'
             _                                                                     -> []
        , ccElements = mapMaybe (genElement _uid) _elements
        }
    genElement _ (IEConstraint True pexp) = Just $ CEConstraint $ genConstraintPExp pexp
    genElement "root" (IEConstraint False pexp) = Just $ CEAssert $ genConstraintPExp pexp
    -- chocosolver's assertions have no context: a nested assertion holds for each instance of its
    -- clafer, so it is quantified over them, with `this` as the local this_, e.g., in clafer P:
    -- assert(all([decl([this_ = local("this_")], global(P))], ... join(this_, age) ...)); the
    -- instances of a nested clafer by the path from its top-level clafer, as clafer resolves
    -- its name, e.g., machine . ctx
    genElement pUID (IEConstraint False pexp) = Just $ CEAssert $
        CQuant IAll [CDecl False [thisLocal] (instancesOf pUID)] (genConstraintPExp (transformOn biplate thisToLocal pexp))
      where
        thisToLocal e@IClaferId{_sident = "this"} = e{_sident = thisLocal}
        thisToLocal e = e
        instancesOf u
            | isTopLevel c = CGlobal u
            | otherwise    = CJoin (instancesOf $ _parentUID c) u
          where
            c = claferWithUid u
    genElement _ (IEGoal isMax PExp{_exp=IFunExp _ [pexp]}) = Just $ CEObjective isMax $ genConstraintPExp pexp
    genElement _ _ = Nothing

    thisLocal = "this_"

    -- the temporal modifiers of a clafer: final, which implies finalref and finaltarget, or the
    -- modifiers of its own reference or of the reference it inherits
    temporalModifiers' IClaferModifiers{_initial, _final, _finalReferences} ref' =
        [ "initial" | _initial ] ++ [ "final" | _final ] ++
        [ refModifierKeyword m | not _final, m <- nub (maybe [] _refModifiers ref' ++ _finalReferences) ]
    refModifierKeyword FinalRef = "finalref"
    refModifierKeyword FinalTarget = "finaltarget"
    refModifierKeyword FinalRefTarget = "final"

    -- a card or group card, unless it is 0..*, which chocosolver has by default
    nonDefault (Just (0, -1)) = Nothing
    nonDefault i              = i

    superOf u =
        case _super $ claferWithUid u of
            Just (PExp{_exp = IClaferId{_sident}})
                | _sident == baseClafer -> Nothing
                | isPrimitive _sident   -> Nothing
                | otherwise             -> Just _sident
            _ -> Nothing

    claferWithUid u = fromMaybe (error $ "claferWithUid: \"" ++ u ++ "\" is not a clafer") $ findIClafer uidIClaferMap' u

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

    -- an empty set of the clafer; with no clafer beside it, e.g., in #noclafer, of the model's
    -- first clafer, since chocosolver neither counts nor quantifies sets of integers
    emptyOf :: Maybe String -> CExp
    emptyOf c = CEmpty $ fromMaybe "Int" (c <|> firstClafer)
    firstClafer = listToMaybe [ _uid c | IEClafer c <- _mDecls ]

    -- the clafer whose instances a set expression is of, e.g., c0_a for a, its type's first; for
    -- an expression of the type of noclafer, e.g., a ** noclafer, that of an operand
    claferOf :: PExp -> Maybe String
    claferOf PExp{_iType = t, _exp = e} = (claferOfType =<< t) <|> case e of
        IFunExp _ args' -> listToMaybe $ mapMaybe claferOf args'
        _ -> Nothing
      where
        claferOfType (TClafer (u : _)) | u `notElem` [noClaferIdent, rootIdent, baseClafer] = Just u
        claferOfType (TMap so _) = claferOfType so
        claferOfType (TUnion (t' : _)) = claferOfType t'
        claferOfType _ = Nothing


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
    genSetExpTarget :: PExp -> [CExp]
    genSetExpTarget ref'
        | Just _ <- setExpType ref', any isPrimitive (getRefIds ref') =
            case member ref' of
                MTrue    -> []
                MFalse   -> [CQuant INo [] CThis]
                MExp e'  -> [e']
        | otherwise = [CFun "$in" [CJoinRef CThis, genConstraintPExp ref']]
      where
        -- membership of the target in a set expression over primitives, as a formula
        member PExp{_exp = IFunExp "++" [a, b]} = mOr (member a) (member b)
        member PExp{_exp = IFunExp "**" [a, b]} = mAnd (member a) (member b)
        member PExp{_exp = IFunExp "--" [a, b]} = mAnd (member a) (mNot $ member b)
        member PExp{_exp = IClaferId{_sident}} | isPrimitive _sident = MTrue
        member e' = MExp $ CFun "equal" [CJoinRef CThis, genConstraintPExp e']
        mOr MTrue _ = MTrue
        mOr _ MTrue = MTrue
        mOr MFalse b = b
        mOr a MFalse = a
        mOr (MExp a) (MExp b) = MExp $ CFun "or" [a, b]
        mAnd MFalse _ = MFalse
        mAnd _ MFalse = MFalse
        mAnd MTrue b = b
        mAnd a MTrue = a
        mAnd (MExp a) (MExp b) = MExp $ CFun "and" [a, b]
        mNot MTrue = MFalse
        mNot MFalse = MTrue
        mNot (MExp a) = MExp $ CFun "not" [a]

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

    genConstraintPExp :: PExp -> CExp
    genConstraintPExp = genConstraintExp . _exp . rewrite

    genConstraintExp :: IExp -> CExp
    genConstraintExp (IDeclPExp quant' decls' body') =
        CQuant quant' (map genDecl decls') (genConstraintPExp body')
        where
            genDecl (IDecl isDisj' locals body'') = CDecl isDisj' locals (genConstraintPExp body'')

    genConstraintExp (IFunExp "." [PExp{_exp = IClaferId{_sident = "root"}}, e2]) =
        genConstraintPExp e2
    genConstraintExp (IFunExp "." [e1, PExp{_exp = IClaferId{_sident = "dref"}}]) =
        CJoinRef $ genConstraintPExp e1
    genConstraintExp (IFunExp "." [e1, PExp{_exp = IClaferId{_sident = "parent"}}]) =
        CJoinParent $ genConstraintPExp e1
    genConstraintExp (IFunExp "." [e1, PExp{_exp = IClaferId{_sident}}]) =
        CJoin (genConstraintPExp e1) _sident
    genConstraintExp (IFunExp "." [_, _]) =
        error "Did not rewrite all joins to left joins."
    genConstraintExp (IFunExp "-" [arg]) =
        CFun "minus" [genConstraintPExp arg]
    genConstraintExp (IFunExp "-" [arg1, arg2]) =
        CFun "sub" [genConstraintPExp arg1, genConstraintPExp arg2]
    genConstraintExp (IFunExp "sum" args')
        | [arg] <- args', PExp{_exp = IFunExp{_exps = [a, PExp{_exp = IClaferId{_sident = "dref"}}]}} <- rewrite arg =
            CFun "sum" [genConstraintPExp a]
        | [arg] <- args' =
            CFun "sum" [genConstraintPExp arg]
        | otherwise = error $ "[bug] Choco.genConstraintExp: Unexpected sum argument: " ++ show args'
    genConstraintExp (IFunExp "product" args')
        | [arg] <- args', PExp{_exp = IFunExp{_exps = [a, PExp{_exp = IClaferId{_sident = "dref"}}]}} <- rewrite arg =
            CFun "product" [genConstraintPExp a]
        | otherwise = error "Choco: Unexpected product argument."
    genConstraintExp (IFunExp "+" args') =
        CFun (if _iType (head args') == Just TString then "concat" else "add") (map genConstraintPExp args')
    genConstraintExp (IFunExp op' args') =
        CFun (mapFunc op') (map genArg args')
        where
            -- noclafer, the empty set, is an empty constant of the type of a set beside it, e.g.,
            -- constant(c0_a) in if some extra then a else noclafer
            genArg a
                | isNoClafer a = emptyOf $ listToMaybe $ mapMaybe claferOf $ filter (not . isNoClafer) args'
                | otherwise    = genConstraintPExp a
    -- noclafer alone, e.g., #noclafer
    genConstraintExp IClaferId{_sident = "noclafer"} = emptyOf Nothing
    genConstraintExp IClaferId{_sident = "this"} = CThis
    genConstraintExp IClaferId{_sident}
        | isJust $ findIClafer uidIClaferMap' _sident = CGlobal _sident
        | otherwise                = CName _sident
    genConstraintExp (IInt val) = CInt val
    genConstraintExp (IStr val) = CStr val
    genConstraintExp (IDouble val) = CDouble val
    genConstraintExp (IDecimal val) = CDecimal $ genDecimal val
    genConstraintExp (IReal _) = error "no real numbers allowed"

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
    -- the temporal operators, which chocosolver does not solve, by their names
    mapFunc op' | op' `elem` ltlOps = op'
    mapFunc op' = error $ "Choco: Unknown op: " ++ op'
