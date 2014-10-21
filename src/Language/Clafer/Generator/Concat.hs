module Language.Clafer.Generator.Concat where

import Data.List
import Data.Maybe
import Language.Clafer.Common
import Language.Clafer.ClaferArgs
import Language.Clafer.Front.Absclafer
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

