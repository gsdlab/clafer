
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
                        module Front.ErrM,
                        module ClaferArgs,
						voidf               
) where

import Data.Maybe
import Control.Monad

import Common
import Front.ErrM
import ClaferArgs
import Front.Lexclafer
import Front.Parclafer
import Front.Printclafer
import Front.Absclafer hiding (Clafer)
import Front.LayoutResolver
import Front.Mapper
import Intermediate.Desugarer
import Intermediate.Resolver
import Intermediate.StringAnalyzer
import Intermediate.Transformer
import Optimizer.Optimizer
import Generator.Alloy
import Generator.Xml
import Generator.Schema
import Generator.Stats

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
claferIRXSD = Generator.Schema.xsd