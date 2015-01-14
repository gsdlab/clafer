{-
 Copyright (C) 2012-2013 Kacper Bak <http://gsd.uwaterloo.ca>

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
module Language.Clafer.Generator.Concat where

import Data.List
import Language.Clafer.Common
import Language.Clafer.Intermediate.Intclafer hiding (exp)

-- | representation of strings in chunks (for line/column numbering)
data Concat = CString String | Concat {
  srcPos :: IrTrace,
  nodes  :: [Concat]
  } deriving (Eq, Show)
type Position = ((LineNo, ColNo), (LineNo, ColNo))

data IrTrace =
    IrPExp {pUid::String} |
    LowerCard {pUid::String, isGroup::Bool} |
    UpperCard {pUid::String, isGroup::Bool} |
    ExactCard {pUid::String, isGroup::Bool} |
    NoTrace
    deriving (Eq, Show)

mkConcat :: IrTrace -> String -> Concat
mkConcat pos str = Concat pos [CString str]

mapToCStr :: [String] -> [Concat]
mapToCStr xs = map CString xs

iscPrimitive :: Concat -> Bool
iscPrimitive x = isPrimitive $ flatten x

flatten :: Concat -> String
flatten (CString x)      = x
flatten (Concat _ nodes') = nodes' >>= flatten

infixr 5 +++
(+++) :: Concat -> Concat -> Concat
(+++) (CString x)     (CString y)     = CString $ x ++ y
(+++) (CString "")    y@Concat{}      = y
(+++) x               y@(Concat src ys)
    | src == NoTrace = Concat NoTrace $ x : ys
    | otherwise      = Concat NoTrace $ [x, y]
(+++) x@Concat{}      (CString "")     = x
(+++) x@(Concat src xs)  y
    | src == NoTrace = Concat NoTrace $ xs ++ [y]
    | otherwise      = Concat NoTrace $ [x, y]

cconcat :: [Concat] -> Concat
cconcat = foldr (+++) (CString "")

cintercalate :: Concat -> [Concat] -> Concat
cintercalate xs xss = cconcat (intersperse xs xss)

filterNull :: [Concat] -> [Concat]
filterNull = filter (not.isNull)

isNull :: Concat -> Bool
isNull (CString "")  = True
isNull (Concat _ []) = True
isNull _ = False

cunlines :: [Concat] -> Concat
cunlines xs = cconcat $ map (+++ (CString "\n")) xs

