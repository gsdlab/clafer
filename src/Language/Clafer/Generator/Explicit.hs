{-# LANGUAGE NamedFieldPuns #-}
{-
 Copyright (C) 2026 Michal Antkiewicz <http://gsd.uwaterloo.ca>

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
-- | Generates the explicit form of a model: the Clafer model the
--   <https://github.com/gsdlab/chocosolver Chocosolver> solves, with nothing left implicit, and
--   its scope file (@clafer -m clafer@, @--meta-data@).
module Language.Clafer.Generator.Explicit (genExplicitModule) where

import Data.List
import qualified Data.Map as Map
import Data.Maybe
import Language.Clafer.Common
import Language.Clafer.Generator.ChocoModel
import Language.Clafer.Intermediate.Intclafer

-- | The explicit form of the model chocosolver solves, and its scope file: a Clafer model with
--   every name a UID, every card, group card, this, parent and dref written out, which starts
--   with @\/\/# OPTIONS --explicit@ (i.e., -f -k -l --ss=none) and compiles to itself; and
--   every scope, as chocosolver's @AstPrinter@ and @ScopeFile@ print them. The [choco| |]
--   escapes, which are JavaScript, are left out.
--   A temporal model has its temporal modifiers and operators, which chocosolver does not
--   read, and its trace length among the options.
genExplicitModule :: (IModule, GEnv) -> [(UID, Integer)] -> (Maybe Integer, Maybe Integer) -> Maybe Integer -> Maybe Integer -> (Result, String)
genExplicitModule ir scopes intRange decimalDigits traceLength =
    let model = chocoModel ir scopes intRange decimalDigits []
    in (explicitModel traceLength model, explicitScopes model)

-- | The explicit model, with the trace length of a temporal model
explicitModel :: Maybe Integer -> CModel -> Result
explicitModel traceLength CModel{cmElements} =
    -- the model declares itself explicit, for clafer and chocosolver
    "//# OPTIONS --explicit" ++ maybe "" (\tl -> " --tl=" ++ show tl) traceLength ++ "\n"
    ++ concat [ "[" ++ exExp e ++ "]\n" | CEConstraint e <- cmElements ]
    ++ concat [ exClafer superMap "" c | CEClafer c <- cmElements ]
    ++ (if null objectives && null assertions then "" else "\n")
    ++ concat [ "<< " ++ (if isMax then "max " else "min ") ++ exExp e ++ " >>\n" | (isMax, e) <- objectives ]
    ++ concat [ "assert [" ++ exExp e ++ "]\n" | e <- assertions ]
  where
    allElements = concatMap preOrder cmElements
    preOrder e@(CEClafer c) = e : concatMap preOrder (ccElements c)
    preOrder e = [e]
    objectives = [ (isMax, e) | CEObjective isMax e <- allElements ]
    assertions = [ e | CEAssert e <- allElements ]
    superMap = Map.fromList [ (ccUid c, c) | CEClafer c <- allElements ]

-- | A clafer with its block: its group card (its own, otherwise its super clafer's, which it
--   inherits), its super clafer, its own reference, its card (0..* if abstract), then its
--   constraints and children
exClafer :: Map.Map UID CClafer -> String -> CClafer -> Result
exClafer superMap indent CClafer{ccUid, ccAbstract, ccModifiers, ccCard, ccGCard, ccSuper, ccRef, ccRefConstraints, ccElements} =
    indent
    ++ (if ccAbstract then "abstract " else "")
    ++ concatMap (++ " ") ccModifiers
    ++ exCard (inheritedGCard ccGCard ccSuper) ++ " "
    ++ ccUid
    ++ maybe "" (" : " ++) ccSuper
    ++ maybe "" (\(isSet', target) -> (if isSet' then " -> " else " ->> ") ++ exTarget target) ccRef
    ++ " " ++ (if ccAbstract then "0..*" else exCard ccCard)
    ++ (if null constraints && null subClafers then " {}\n"
        else " {\n"
             ++ concat [ indent' ++ "[" ++ exExp e ++ "]\n" | e <- constraints ]
             ++ concatMap (exClafer superMap indent') subClafers
             ++ indent ++ "}\n")
  where
    indent' = indent ++ "  "
    constraints = ccRefConstraints ++ [ e | CEConstraint e <- ccElements ]
    subClafers = [ c | CEClafer c <- ccElements ]
    inheritedGCard g@(Just _) _ = g
    inheritedGCard Nothing (Just s) | Just CClafer{ccGCard = g, ccSuper = s'} <- Map.lookup s superMap = inheritedGCard g s'
    inheritedGCard _ _ = Nothing
    exTarget "integer" = "int"
    exTarget target = target

exCard :: Maybe Interval -> String
exCard (Just (low, high)) = show low ++ ".." ++ (if high < 0 then "*" else show high)
exCard Nothing            = "0..*"

-- | An expression, fully parenthesized except for navigation, which binds tightest
exExp :: CExp -> String
exExp CThis = "this"
exExp (CGlobal u) = u
exExp (CName n) = n
exExp (CInt val) = show val
exExp (CStr val) = val
exExp (CDouble val) = show val
exExp (CDecimal val) = val
exExp (CEmpty _) = "noclafer"
exExp (CJoin e c) = exOperand e ++ "." ++ c
exExp (CJoinRef e) = exOperand e ++ ".dref"
exExp (CJoinParent e) = exOperand e ++ ".parent"
-- chocosolver's quantifiers over a set compare its size, e.g., none(x) is #x = 0
exExp (CQuant q [] set) = case q of
    INo   -> sizeIs "=" 0
    ISome -> sizeIs ">=" 1
    ILone -> sizeIs "<=" 1
    IOne  -> sizeIs "=" 1
    IAll  -> "all " ++ exOperand set
  where
    sizeIs op' n = "(#" ++ exOperand set ++ ") " ++ op' ++ " " ++ show (n :: Integer)
exExp (CQuant q decls' body') = exQuant q ++ " " ++ intercalate ", " (map exDecl decls') ++ " | " ++ exExp body'
  where
    exDecl (CDecl isDisj' locals set) = (if isDisj' then "disj " else "") ++ intercalate "; " locals ++ " : " ++ exExp set
exExp (CFun f args') = case (f, args') of
    ("not", [a])       -> "!" ++ exOperand a
    -- -1 is a constant, so the negation of a number is -(1)
    ("minus", [a])     -> "-" ++ (if isConstant a then "(" ++ exExp a ++ ")" else exOperand a)
    ("card", [a])      -> "#" ++ exOperand a
    ("sum", [a])       -> "sum " ++ exOperand a ++ ".dref"
    ("product", [a])   -> "product " ++ exOperand a ++ ".dref"
    ("maximum", [a])   -> "max " ++ exOperand a
    ("minimum", [a])   -> "min " ++ exOperand a
    ("concat", [a, b]) -> "concat(" ++ exExp a ++ ", " ++ exExp b ++ ")"
    ("ifThenElse", [a, b, c]) -> "if " ++ exOperand a ++ " then " ++ exOperand b ++ " else " ++ exOperand c
    -- the temporal operators F, G, X, initially and finally; U and W are binary operators
    (_, [a]) | f `elem` ltlUnOps -> f ++ " " ++ exOperand a
    (_, [a, b]) | Just op' <- lookup f binaryOps -> exOperand a ++ " " ++ op' ++ " " ++ exOperand b
    _ -> error $ "Choco: no explicit form of " ++ f
  where
    isConstant CInt{} = True
    isConstant CDecimal{} = True
    isConstant CEmpty{} = True
    isConstant _ = False
    binaryOps =
        [ ("add", "+"), ("sub", "-"), ("mul", "*"), ("div", "/"), ("mod", "%")
        , ("and", "&&"), ("or", "||"), ("implies", "=>"), ("ifOnlyIf", "<=>"), ("xor", "xor")
        , ("lessThan", "<"), ("lessThanEqual", "<="), ("greaterThan", ">"), ("greaterThanEqual", ">=")
        , ("equal", "="), ("notEqual", "!="), ("$in", "in"), ("notIn", "not in")
        , ("union", "++"), ("diff", "--"), ("inter", "**"), ("U", "U"), ("W", "W") ]

exQuant :: IQuant -> String
exQuant INo = "no"
exQuant ISome = "some"
exQuant IAll = "all"
exQuant IOne = "one"
exQuant ILone = "lone"

-- | An operand: navigation and atoms as they are, other expressions in parentheses
exOperand :: CExp -> String
exOperand e
    | isAtom e = exExp e
    | otherwise = "(" ++ exExp e ++ ")"
  where
    isAtom CThis = True
    isAtom CGlobal{} = True
    isAtom CName{} = True
    isAtom CInt{} = True
    isAtom CStr{} = True
    isAtom CDouble{} = True
    isAtom CDecimal{} = True
    isAtom CEmpty{} = True
    isAtom CJoin{} = True
    isAtom CJoinRef{} = True
    isAtom CJoinParent{} = True
    isAtom (CFun "concat" _) = True
    isAtom _ = False

-- | The scope file of the explicit form: every clafer's scope by its UID, sorted, then the
--   default scope and the ranges, as chocosolver's ScopeFile prints the scope it solves with
explicitScopes :: CModel -> String
explicitScopes CModel{cmElements, cmScope = CScope{csClafers, csIntRange, csStringLength, csDecimalScale}} =
    "[\n" ++ intercalate ",\n" entries ++ "\n]\n"
  where
    uids = sort [ ccUid c | CEClafer c <- concatMap preOrder cmElements ]
    preOrder e@(CEClafer c) = e : concatMap preOrder (ccElements c)
    preOrder e = [e]
    (intLow, intHigh) = fromMaybe (-128, 127) csIntRange
    scale = fromMaybe 0 csDecimalScale
    -- the largest decimal: chocosolver's Integer.MAX_VALUE / 100 - 1, scaled
    maxScaledDecimal = 21474835 :: Integer
    entries =
        [ "{\"lpqName\": \"" ++ u ++ "\", \"scope\": " ++ show (fromMaybe 1 $ lookup u csClafers) ++ "}" | u <- uids ]
        ++ [ "{\"defaultScope\": 1}"
           , "{\"int\": [" ++ show intLow ++ ", " ++ show intHigh ++ "]}"
           , "{\"mul\": [" ++ show intLow ++ ", " ++ show intHigh ++ "]}"
           , "{\"stringLength\": " ++ show csStringLength ++ "}"
           , "{\"chars\": [32, 126]}"
           , "{\"decimalDigits\": " ++ show scale ++ "}"
           , "{\"decimal\": [" ++ unscaled (-maxScaledDecimal) ++ ", " ++ unscaled maxScaledDecimal ++ "]}" ]
    -- a scaled decimal as written, e.g., 214748.35 for 21474835 with 2 digits
    unscaled n =
        let digits = show (abs n)
            padded = replicate (fromIntegral scale + 1 - length digits) '0' ++ digits
            (whole, fraction) = splitAt (length padded - fromIntegral scale) padded
        in (if n < 0 then "-" else "") ++ whole ++ (if scale > 0 then "." ++ fraction else "")
