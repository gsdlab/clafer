{-
 Copyright (C) 2012 Kacper Bak, Jimmy Liang, Michal Antkiewicz <http://gsd.uwaterloo.ca>

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
module Language.Clafer (
                        myLexer,  -- don't want to export (addFragment)
                        resolveLayout,-- don't want to export (addFragment)
                        resLayout, -- don't want to export (addFragment)
                        desugar,
                        analyze,
                        generate,
                        Token,
                        pModule,
                        Module,
                        claferIRXSD,
                        module Language.Clafer.Front.ErrM,
                        module Language.Clafer.ClaferArgs,
                        voidf               
) where

import Data.Maybe
import Control.Monad

import Language.Clafer.Common
import Language.Clafer.Front.ErrM
import Language.Clafer.ClaferArgs
import Language.Clafer.Front.Lexclafer
import Language.Clafer.Front.Parclafer
import Language.Clafer.Front.Printclafer
import Language.Clafer.Front.Absclafer hiding (Clafer)
import Language.Clafer.Front.LayoutResolver
import Language.Clafer.Front.Mapper
import Language.Clafer.Intermediate.Desugarer
import Language.Clafer.Intermediate.Resolver
import Language.Clafer.Intermediate.StringAnalyzer
import Language.Clafer.Intermediate.Transformer
import Language.Clafer.Optimizer.Optimizer
import Language.Clafer.Generator.Alloy
import Language.Clafer.Generator.Xml
import Language.Clafer.Generator.Schema
import Language.Clafer.Generator.Stats

desugar args tree = do
--  conPutStrLn args "[Desugaring]"
  let dTree = desugarModule $ mapModule tree
  return dTree
  -- writeFile (f ++ ".des") $ printTree $
  --  sugarModule dTree

analyze args tree = do
  let dTree' = findDupModule args tree
  let au = allUnique dTree'
  let args' = args{skip_resolver = Just $ au && (fromJust $ skip_resolver args)}
--  conPutStrLn args "[Resolving]"
  let (rTree, genv) = resolveModule args' dTree'
--  conPutStrLn args "[Transforming]"
  let tTree = transModule rTree
--  conPutStrLn args "[Optimizing]"
  return $ (optimizeModule args' (tTree, genv), genv, au)
  -- writeFile (f ++ ".ana") $ printTree $
  --  sugarModule oTree

  
generate f args (oTree, genv, au) = do
--  conPutStrLn args "[Generating Code]"
  let stats = showStats au $ statsModule oTree
  when (not $ fromJust $ no_stats args) $ putStrLn stats
--  conPutStrLn args "[Saving File]"
  let alloyCode = genModule args (astrModule oTree, genv)
  let addCommentStats = if fromJust $ no_stats args then const else addStats
  let (ext, code) = case (fromJust $ mode args) of
                      Alloy   -> ("als", addCommentStats (fst alloyCode) stats)
                      Alloy42 -> ("als", addCommentStats (fst alloyCode) stats)
                      Xml     -> ("xml", genXmlModule oTree)
                      Clafer  -> ("des.cfr", printTree $ sugarModule oTree)
  let f' = f ++ "." ++ ext
  if fromJust $ console_output args then putStrLn code else writeFile f' code
  let mf = f ++ "." ++ "map"
  when (fromJust $ alloy_mapping args) $ writeFile mf $ show $ snd alloyCode
  return f'
  
addStats code stats = "/*\n" ++ stats ++ "*/\n" ++ code


showStats au (Stats na nr nc nconst ngoals sgl) =
  unlines [ "All clafers: " ++ (show (na + nr + nc)) ++ " | Abstract: " ++ (show na) ++ " | Concrete: " ++ (show nc) ++ " | References: " ++ (show nr)          , "Constraints: " ++ show nconst
          , "Goals: " ++ show ngoals  
          , "Global scope: " ++ showInterval sgl
          , "All names unique: " ++ show au]


showInterval (n, -1) = show n ++ "..*"
showInterval (n, m) = show n ++ ".." ++ show m

claferIRXSD :: [Char]
claferIRXSD = Language.Clafer.Generator.Schema.xsd