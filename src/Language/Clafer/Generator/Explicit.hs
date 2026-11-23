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
module Language.Clafer.Generator.Explicit (genExplicitModule, withoutOrigins) where

import Data.List
import qualified Data.Map as Map
import Numeric (showEFloat)
import Data.Maybe
import Language.Clafer.Common
import Language.Clafer.Front.AbsClafer (Pos (..), Span (..), noPos)
import Language.Clafer.Generator.ChocoModel
import Language.Clafer.Intermediate.Intclafer

-- | The explicit form of the model, and its scope file: a Clafer model with every name a UID,
--   every card, group card, this, parent and dref written out, which starts with
--   @\/\/# OPTIONS --explicit@ (i.e., -f -k -l --ss=none) and compiles to itself; and every
--   scope, as chocosolver's @AstPrinter@ and @ScopeFile@ print them. The [choco| |] escapes,
--   which are JavaScript, are left out.
--   The explicit model keeps the enumerations, initializers, behavioral patterns and
--   transitions, and writes the clock of every initializer @:=@, @:= each@ or @:= together@
--   (kbak/clafer-semantics#194), so that its meaning does not depend on the multiplicity; its core, from the IR that "Language.Clafer.Intermediate.Core" lowers, is
--   what the backends solve (for a static model, what chocosolver solves).
--   A temporal model has its temporal modifiers and operators, which chocosolver does not
--   read, and its trace length among the options.
--   The explicit core model declares itself the core (@--core@), so that it compiles to itself.
--   The origins of @--record-provenance@ are positions as in the messages, @file:line:column@,
--   which the given function makes of a position of the model.
genExplicitModule :: Bool -> (Pos -> String) -> (IModule, GEnv) -> [(UID, Integer)] -> (Maybe Integer, Maybe Integer) -> Maybe Integer -> Maybe Integer -> (Result, String)
genExplicitModule core' position ir scopes intRange decimalDigits traceLength =
    let model = chocoModel ir scopes intRange decimalDigits []
    in (explicitModel core' position traceLength model, explicitScopes model)

-- | The explicit model, with the trace length of a temporal model
explicitModel :: Bool -> (Pos -> String) -> Maybe Integer -> CModel -> Result
explicitModel core' position traceLength CModel{cmElements} =
    -- the model declares itself explicit, for clafer and chocosolver, and the core
    "//# OPTIONS --explicit" ++ (if core' then " --core" else "") ++ maybe "" (\tl -> " --tl=" ++ show tl) traceLength ++ "\n"
    -- the top-level declarations where they were written; an enumeration with its literals
    ++ concatMap exTop cmElements
    ++ (if null objectives && null assertions then "" else "\n")
    ++ concat [ "<< " ++ (if isMax then "max " else "min ") ++ exExp e ++ " >>\n" | (isMax, e) <- objectives ]
    ++ concat [ "assert [" ++ exExp e ++ "]" ++ exOrigin o ++ "\n" | (o, e) <- assertions ]
  where
    allElements = concatMap preOrder cmElements
    preOrder e@(CEClafer c) = e : concatMap preOrder (ccElements c)
    preOrder e = [e]
    objectives = [ (isMax, e) | CEObjective isMax e <- allElements ]
    assertions = [ (o, e) | CEAssert o e <- allElements ]
    superMap = Map.fromList [ (ccUid c, c) | CEClafer c <- allElements ]
    exOrigin = originComment position
    exTop (CEConstraint o e) = "[" ++ exExp e ++ "]" ++ exOrigin o ++ "\n"
    exTop (CEClafer c)
      | isEnum c = if ccAbstract c then exEnum c else ""
      | otherwise = exClafer exOrigin superMap "" c
    exTop _ = ""
    -- an enumeration, with its literals in their order
    exEnum c = "enum " ++ ccUid c ++ " = "
        ++ intercalate " | " [ ccUid l | CEClafer l <- cmElements, isEnum l, ccSuper l == Just (ccUid c) ] ++ "\n"

-- | Whether the clafer is an enumeration or one of its literals.
isEnum :: CClafer -> Bool
isEnum c = "enum" `elem` ccModifiers c

-- | A clafer with its block: its group card (its own, otherwise its super clafer's, which it
--   inherits), its super clafer, its own reference, its card (0..* if abstract), then its
--   constraints and children
exClafer :: (Maybe Origin -> String) -> Map.Map UID CClafer -> String -> CClafer -> Result
exClafer exOrigin superMap indent CClafer{ccUid, ccAbstract, ccModifiers, ccCard, ccGCard, ccSuper, ccRef, ccRefConstraints, ccElements, ccOrigin} =
    indent
    ++ (if ccAbstract then "abstract " else "")
    ++ concatMap (++ " ") (filter (/= "enum") ccModifiers)
    ++ exCard (inheritedGCard ccGCard ccSuper) ++ " "
    ++ ccUid
    ++ maybe "" (" : " ++) ccSuper
    ++ maybe "" (\(isSet', target) -> (if isSet' then " -> " else " ->> ") ++ exTarget target) ccRef
    -- the multiplicity of an abstract clafer bounds the number of all its instances (#129)
    ++ (if ccAbstract
        then (if ccCard `elem` [Nothing, Just (0, -1)] then " 0..*" else " " ++ exCard ccCard)
        else " " ++ exCard ccCard)
    -- the initializer as written, with its clock, and its value in the context of the parent
    ++ concat [ (if k then " = " else if s then " := together " else " := each ") ++ exExp e | CEInitializer k s e <- ccElements ]
    ++ (if isEmptyBody then " {}" ++ exOrigin ccOrigin ++ "\n"
        else " {" ++ exOrigin ccOrigin ++ "\n"
             -- the constraints of the reference, then the constraints and subclafers where
             -- they were written
             ++ concat [ exConstraint Nothing e | e <- ccRefConstraints ]
             ++ concatMap exBody ccElements
             ++ indent ++ "}\n")
  where
    indent' = indent ++ "  "
    exConstraint o e = indent' ++ "[" ++ exExp e ++ "]" ++ exOrigin o ++ "\n"
    exBody (CEConstraint o e) = exConstraint o e
    exBody (CEClafer c) = exClafer exOrigin superMap indent' c
    exBody _ = ""
    isEmptyBody = null ccRefConstraints && null [ () | e <- ccElements, isBody e ]
    isBody CEConstraint{} = True
    isBody CEClafer{} = True
    isBody _ = False
    inheritedGCard g@(Just _) _ = g
    inheritedGCard Nothing (Just s) | Just CClafer{ccGCard = g, ccSuper = s'} <- Map.lookup s superMap = inheritedGCard g s'
    inheritedGCard _ _ = Nothing
    exTarget "integer" = "int"
    exTarget target = target

-- | The comment with the origin of a construct of the core, @--record-provenance@: the rich
--   construct that a lowering made it from, and the position of that construct, as in the
--   messages, e.g., @// final, model.cfr:56:5@.
originComment :: (Pos -> String) -> Maybe Origin -> String
originComment _ Nothing = ""
originComment position (Just Origin{_construct, _originPos = Span start _})
  | start /= noPos = " // " ++ _construct ++ ", " ++ position start
  | otherwise = " // " ++ _construct

-- | The explicit model without the comments of the origins, which a core with them compiles to:
--   a comment at the end of a line that ends with a position, @line:column@.
withoutOrigins :: String -> String
withoutOrigins = unlines . map withoutOrigin . lines
  where
  withoutOrigin l = case breakLast " // " l of
    Just (code, comment) | endsWithPosition comment -> code
    _ -> l
  breakLast sep s = case [ i | i <- [0 .. length s - length sep], sep `isPrefixOf` drop i s ] of
    [] -> Nothing
    is -> let i = last is in Just (take i s, drop (i + length sep) s)
  endsWithPosition comment = case reverse (splitOn' ':' comment) of
    column' : line' : _ -> isNumber' column' && isNumber' (lastWord line')
    _ -> False
  lastWord = reverse . takeWhile (`notElem` " ,") . reverse
  isNumber' s = not (null s) && all (`elem` ['0' .. '9']) s
  splitOn' c s = case break (== c) s of
    (a, []) -> [a]
    (a, _ : rest) -> a : splitOn' c rest

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
-- with an exponent, e.g., 1.2e2, which the token of a double literal has
exExp (CDouble val) = showEFloat Nothing val ""
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
exExp (CFun f args')
    | Just (kind, scope) <- patternOf f = exPattern kind scope args'
    | f `elem` transitionOps = exTransition f args'
exExp (CFun f args') = case (f, args') of
    ("not", [a])       -> "!" ++ exOperand a
    -- -1 is a constant, so the negation of a number is -(1)
    ("minus", [a])     -> "-" ++ (if isConstantExp a then "(" ++ exExp a ++ ")" else exOperand a)
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
    isConstantExp CInt{} = True
    isConstantExp CDecimal{} = True
    isConstantExp CEmpty{} = True
    isConstantExp _ = False
    binaryOps =
        [ ("add", "+"), ("sub", "-"), ("mul", "*"), ("div", "/"), ("mod", "%")
        , ("and", "&&"), ("or", "||"), ("implies", "=>"), ("ifOnlyIf", "<=>"), ("xor", "xor")
        , ("lessThan", "<"), ("lessThanEqual", "<="), ("greaterThan", ">"), ("greaterThanEqual", ">=")
        , ("equal", "="), ("notEqual", "!="), ("$in", "in"), ("notIn", "not in")
        , ("union", "++"), ("diff", "--"), ("inter", "**"), ("U", "U"), ("W", "W"), ("since", "since"), ("triggered", "triggered") ]

-- | A behavioral pattern, e.g., @s must precede p after q until r@.
exPattern :: String -> String -> [CExp] -> String
exPattern kind scope args' = pat ++ exScope scope scopeArgs
  where
    (own, scopeArgs) = splitAt (if kind `elem` ["precede", "follow"] then 2 else 1) args'
    pat = case (kind, own) of
      (_, [s, p]) -> exOperand s ++ " must " ++ kind ++ " " ++ exOperand p
      (_, [p])    -> kind ++ " " ++ exOperand p
      _           -> error $ "Explicit.exPattern: " ++ kind
    exScope "" [] = ""
    exScope "before" [r] = " before " ++ exOperand r
    exScope "after" [q] = " after " ++ exOperand q
    exScope "between" [q, r] = " between " ++ exOperand q ++ " and " ++ exOperand r
    exScope "after until" [q, r] = " after " ++ exOperand q ++ " until " ++ exOperand r
    exScope s _ = error $ "Explicit.exPattern: scope " ++ s

-- | A transition, whose target may be a chain of transitions; the context instance of @-->>@
--   is not written.
exTransition :: String -> [CExp] -> String
exTransition f args' = case (f, args') of
    (_, [a, b]) | f == iTrans -> exOperand a ++ " --> " ++ target b
    (_, [a, g, b]) | f == iTransGuarded -> exOperand a ++ " -[" ++ exOperand g ++ "]-> " ++ target b
    (_, a : b : _) | f == iTransSync -> exOperand a ++ " -->> " ++ target b
    (_, a : g : b : _) | f == iTransSyncGuarded -> exOperand a ++ " -[" ++ exOperand g ++ "]->> " ++ target b
    _ -> error $ "Explicit.exTransition: " ++ f
  where
    target b@(CFun f' _) | f' `elem` transitionOps = exExp b
    target b = exOperand b

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
