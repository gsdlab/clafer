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

import Data.List
import Language.Clafer.Common
import Language.Clafer.Front.LexClafer
import Language.Clafer.Generator.ChocoModel
import Language.Clafer.Intermediate.Intclafer

-- | Choco 3 code generation, with the given smallest and largest integers, if any, and the
--   number of fractional digits of decimals, if given
genCModule :: (IModule, GEnv) -> [(UID, Integer)] -> (Maybe Integer, Maybe Integer) -> Maybe Integer -> [Token] -> Result
genCModule ir scopes intRange decimalDigits otherTokens' = jsModel $ chocoModel ir scopes intRange decimalDigits otherTokens'

jsModel :: CModel -> Result
jsModel CModel{cmElements, cmScope, cmEscapes} =
    jsScope cmScope
    ++ "\n"
    ++ (jsClafer =<< cmElements)
    ++ (jsLinks "root" =<< cmElements)
    ++ cmEscapes

jsScope :: CScope -> Result
jsScope CScope{csClafers, csIntRange, csStringLength, csDecimalScale} =
    (if null csClafers then "" else "scope({" ++ intercalate ", " [uid' ++ ":" ++ show scope | (uid', scope) <- csClafers] ++ "});\n")
    ++ "defaultScope(1);\n"
    ++ maybe "" (\(low, high) -> "intRange(" ++ show low ++ ", " ++ show high ++ ");\n") csIntRange
    ++ "stringLength(" ++ show csStringLength ++ ");\n"
    ++ maybe "" (\scale -> "decimalScale(" ++ show scale ++ ");\n") csDecimalScale

-- | The clafers, nested
jsClafer :: CElement -> Result
jsClafer (CEClafer CClafer{ccUid, ccParent, ccAbstract, ccCard, ccGCard, ccElements}) =
    ccUid
    ++ nesting
    ++ prop "withGroupCard" (jsCard ccGCard)
    ++ ";\n"
    ++ (jsClafer =<< ccElements)
  where
    nesting
        | ccAbstract && ccParent == "clafer" = " = Abstract(\"" ++ ccUid ++ "\")"
        | ccAbstract                         = " = " ++ ccParent ++ ".addAbstractChild(\"" ++ ccUid ++ "\")"
        | ccParent == "root"                 = " = Clafer(\"" ++ ccUid ++ "\")" ++ prop "withCard" (jsCard ccCard)
        | otherwise                          = " = " ++ ccParent ++ ".addChild(\"" ++ ccUid ++ "\")" ++ prop "withCard" (jsCard ccCard)
jsClafer _ = ""

-- | The super clafers, references, constraints, objectives and assertions, in the context of a clafer
jsLinks :: String -> CElement -> Result
jsLinks _ (CEClafer CClafer{ccUid, ccLinked, ccSuper, ccRef, ccRefConstraints, ccElements})
    | ccLinked =
        ccUid
        ++ prop "extending" ccSuper
        ++ maybe "" refTo ccRef
        ++ ";\n"
        ++ concatMap (\c -> ccUid ++ ".addConstraint(" ++ jsExp c ++ ");\n") ccRefConstraints
        ++ (jsLinks ccUid =<< ccElements)
    | otherwise = jsLinks ccUid =<< ccElements
  where
    refTo (True, target)  = ".refToUnique(" ++ jsTarget target ++ ")"
    refTo (False, target) = ".refTo(" ++ jsTarget target ++ ")"
    jsTarget "integer" = "Int"
    jsTarget "int" = "Int"
    jsTarget "decimal" = "Decimal"
    jsTarget target = target
jsLinks "root" (CEConstraint e) = "Constraint(" ++ jsExp e ++ ");\n"
jsLinks pUID (CEConstraint e) = pUID ++ ".addConstraint(" ++ jsExp e ++ ");\n"
jsLinks _ (CEAssert e) = "assert(" ++ jsExp e ++ ");\n"
jsLinks _ (CEObjective True e) = "max(" ++ jsExp e ++ ");\n"
jsLinks _ (CEObjective False e) = "min(" ++ jsExp e ++ ");\n"

prop :: String -> Maybe String -> String
prop name = maybe "" (\value -> "." ++ name ++ "(" ++ value ++ ")")

jsCard :: Maybe Interval -> Maybe String
jsCard (Just (low, -1))   = Just $ show low
jsCard (Just (low, high)) = Just $ show low ++ ", " ++ show high
jsCard Nothing            = Nothing

jsExp :: CExp -> String
jsExp CThis = "$this()"  -- this is a keyword in Javascript
jsExp (CGlobal u) = "global(" ++ u ++ ")"
jsExp (CName n) = n
jsExp (CInt val) = "constant(" ++ show val ++ ")"
jsExp (CStr val) = "constant(" ++ show val ++ ")"
jsExp (CDouble val) = "constant(" ++ show val ++ ")"
jsExp (CDecimal val) = "decimal(\"" ++ val ++ "\")"
jsExp (CEmpty c) = "constant(" ++ c ++ ")"
jsExp (CJoin e c) = "join(" ++ jsExp e ++ ", " ++ c ++ ")"
jsExp (CJoinRef e) = "joinRef(" ++ jsExp e ++ ")"
jsExp (CJoinParent e) = "joinParent(" ++ jsExp e ++ ")"
jsExp (CFun f args') = f ++ "(" ++ intercalate ", " (map jsExp args') ++ ")"
jsExp (CQuant q [] body') = jsQuant q ++ "(" ++ jsExp body' ++ ")"
jsExp (CQuant q decls' body') =
    jsQuant q ++ "([" ++ intercalate ", " (map jsDecl decls') ++ "], " ++ jsExp body' ++ ")"
  where
    jsDecl (CDecl isDisj' locals body'') =
        (if isDisj' then "disjDecl" else "decl") ++ "([" ++ intercalate ", " (map jsLocal locals) ++ "], " ++ jsExp body'' ++ ")"
    jsLocal local = local ++ " = local(\"" ++ local ++ "\")"

jsQuant :: IQuant -> String
jsQuant INo = "none"
jsQuant ISome = "some"
jsQuant IAll = "all"
jsQuant IOne = "one"
jsQuant ILone = "lone"
