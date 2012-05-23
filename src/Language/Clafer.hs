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
                        addModuleFragment,
                        compile,
                        generate, 
                        claferIRXSD,
                        VerbosityL,
                        InputModel,
                        Token,
                        Module,
                        GEnv,
                        IModule,
                        module Language.Clafer.Front.ErrM,
                        module Language.Clafer.ClaferArgs,
                        voidf
                                       
) where

import Data.Maybe
import Control.Monad()

import Language.Clafer.Common
import Language.Clafer.Front.ErrM
import Language.Clafer.ClaferArgs
import Language.Clafer.Front.Lexclafer
import Language.Clafer.Front.Parclafer
import Language.Clafer.Front.Printclafer
import Language.Clafer.Front.Absclafer hiding (Clafer)
import Language.Clafer.Front.LayoutResolver
import Language.Clafer.Front.Mapper
import Language.Clafer.Intermediate.Intclafer
import Language.Clafer.Intermediate.Desugarer
import Language.Clafer.Intermediate.Resolver
import Language.Clafer.Intermediate.StringAnalyzer
import Language.Clafer.Intermediate.Transformer
import Language.Clafer.Optimizer.Optimizer
import Language.Clafer.Generator.Alloy
import Language.Clafer.Generator.Xml
import Language.Clafer.Generator.Schema
import Language.Clafer.Generator.Stats

type VerbosityL = Int
type InputModel = String

addModuleFragment :: ClaferArgs -> InputModel -> Err Module
addModuleFragment args inputModel = 
  let inputTokens = (if not 
                  ((fromJust $ new_layout args) ||
                  (fromJust $ no_layout args))
                then 
                   resolveLayout 
                else 
                   id) 
                $ myLexer $
                (if (not $ fromJust $ no_layout args) &&
                    (fromJust $ new_layout args)
                 then 
                   resLayout 
                 else 
                   id)
                inputModel
  in pModule inputTokens

compile :: ClaferArgs -> Module -> (IModule, GEnv, Bool)
compile args tree = analyze args $ desugar tree

generate :: ClaferArgs -> (IModule, GEnv, Bool) -> (String, String, String, Maybe String)
generate args (iModule, genv, au) = do
  let stats = showStats au $ statsModule iModule
  let (ext, code, mappingToAlloy) = case (fromJust $ mode args) of
                      Alloy   -> do
                                   let alloyCode = genModule args (astrModule iModule, genv)
                                   let addCommentStats = if fromJust $ no_stats args then const else addStats
                                   let m = show $ snd alloyCode
                                   ("als", addCommentStats (fst alloyCode) stats, Just m)
                      Alloy42 -> do
                                   let alloyCode = genModule args (astrModule iModule, genv)
                                   let addCommentStats = if fromJust $ no_stats args then const else addStats
                                   let m = show $ snd alloyCode
                                   ("als", addCommentStats (fst alloyCode) stats, Just m)
                      Xml     -> ("xml", genXmlModule iModule, Nothing)
                      Clafer  -> ("des.cfr", printTree $ sugarModule iModule, Nothing)
  (ext, code, stats, mappingToAlloy)
  
desugar :: Module -> IModule  
desugar tree = do
  desugarModule $ mapModule tree

analyze :: ClaferArgs -> IModule -> (IModule, GEnv, Bool)
analyze args tree = do
  let dTree' = findDupModule args tree
  let au = allUnique dTree'
  let args' = args{skip_resolver = Just $ au && (fromJust $ skip_resolver args)}
  let (rTree, genv) = resolveModule args' dTree'
  let tTree = transModule rTree
  (optimizeModule args' (tTree, genv), genv, au)

addStats :: String -> String -> String
addStats code stats = "/*\n" ++ stats ++ "*/\n" ++ code

showStats :: Bool -> Stats -> String
showStats au (Stats na nr nc nconst ngoals sgl) =
  unlines [ "All clafers: " ++ (show (na + nr + nc)) ++ " | Abstract: " ++ (show na) ++ " | Concrete: " ++ (show nc) ++ " | References: " ++ (show nr)          , "Constraints: " ++ show nconst
          , "Goals: " ++ show ngoals  
          , "Global scope: " ++ showInterval sgl
          , "All names unique: " ++ show au]

showInterval :: (Integer, Integer) -> String
showInterval (n, -1) = show n ++ "..*"
showInterval (n, m) = show n ++ ".." ++ show m

claferIRXSD :: String
claferIRXSD = Language.Clafer.Generator.Schema.xsd