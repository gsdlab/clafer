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
                        parse,
                        generate,
                        generateHtml,
                        generateFragments,
                        runClaferT,
                        runClafer,
                        ClaferErr(..),
                        throwError,
                        catchError,
                        getEnv,
                        putEnv,
                        CompilerResult(..),
                        claferIRXSD,
                        VerbosityL,
                        InputModel,
                        Token,
                        Module,
                        GEnv,
                        IModule,
                        voidf,
                        ClaferEnv(..),
                        ir,
                        ast,
                        makeEnv,
                        module Language.Clafer.ClaferArgs,
                        module Language.Clafer.Front.ErrM,
                                       
) where

import Data.List
import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Ord
import Control.Monad()
import Control.Monad.Error
import Control.Monad.State
import Control.Monad.Identity
import System.FilePath.Posix (dropExtension)

import Language.Clafer.Common
import Language.Clafer.Front.ErrM
import Language.Clafer.ClaferArgs
import Language.Clafer.Comments
import qualified Language.Clafer.Css as Css
import Language.Clafer.Front.Lexclafer
import Language.Clafer.Front.Parclafer
import Language.Clafer.Front.Printclafer
import Language.Clafer.Front.Absclafer hiding (Clafer)
import Language.Clafer.Front.LayoutResolver
import Language.Clafer.Front.Mapper
import Language.Clafer.Intermediate.Tracing
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
import Language.Clafer.Generator.Html
import Language.Clafer.Generator.Graph

type VerbosityL = Int
type InputModel = String

{- Example of compiling a model consisting of one fragment:
 -  compileOneFragment :: ClaferArgs -> InputModel -> Either ClaferErr CompilerResult
 -  compileOneFragment args model =
 -    runClafer args $
 -      do
 -        addModuleFragment model
 -        parse
 -        compile
 -        generate
 -
 -
 - Use "generateFragments" instead to generate output based on their fragments.
 -  compileTwoFragments :: ClaferArgs -> InputModel -> InputModel -> Either ClaferErr [String]
 -  compileTwoFragments args frag1 frag2 =
 -    runClafer args $
 -      do
 -        addModuleFragment frag1
 -        addModuleFragment frag2
 -        parse
 -        compile
 -        generateFragments
 -
 - Use "throwError" to halt execution:
 -  runClafer args $
 -    when (notValid args) $ throwError (ClaferErr "Invalid arguments.")
 -}

data ClaferEnv = ClaferEnv {
                            args :: ClaferArgs, 
                            model :: String,    -- original text of the model
                            cAst :: Maybe Module,
                            cIr :: Maybe (IModule, GEnv, Bool),
                            frags :: [Pos],    -- line numbers of fragment markers
                            irModuleTrace :: Map Span [Ir],
                            astModuleTrace :: Map Span [Ast]
                            } deriving Show
ast ClaferEnv{cAst = Just a} = a
ast _ = error "No AST. Did you forget to add fragments or parse?" -- Indicates a bug in the Clafer translator.

ir ClaferEnv{cIr = Just i} = i
ir _ = error "No IR. Did you forget to compile?" -- Indicates a bug in the Clafer translator.
                            
makeEnv args model = ClaferEnv { args = args,
                                 model = model,
                                 cAst = Nothing,
                                 cIr = Nothing,
                                 frags = [],
                                 irModuleTrace = Map.empty,
                                 astModuleTrace = Map.empty}

type ClaferM = ClaferT Identity
-- Monad for using Clafer.
type ClaferT m = ErrorT ClaferErr (StateT ClaferEnv m)

-- Possible errors that can occur when using Clafer
-- Generate errors using throwError:
--   throwError $ ClaferErr "Example of an error."
data ClaferErr =
  ClaferErr String |  -- Generic error
  ParseErr String     -- Error generated by the parser
  deriving Show

instance Error ClaferErr where
  noMsg = ClaferErr ""
  strMsg = ClaferErr

-- Get the ClaferEnv
getEnv :: Monad m => ClaferT m ClaferEnv
getEnv = get

-- Modify the ClaferEnv
modifyEnv :: Monad m => (ClaferEnv -> ClaferEnv) -> ClaferT m ()
modifyEnv = modify

-- Set the ClaferEnv. Remember to set the env after every change.
putEnv :: Monad m => ClaferEnv -> ClaferT m ()
putEnv = put

-- Uses the ErrorT convention:
--   Left is for error (a string containing the error message)
--   Right is for success (with the result)
runClaferT :: Monad m => ClaferArgs -> ClaferT m a -> m (Either ClaferErr a)
runClaferT args exec = evalStateT (runErrorT exec) (makeEnv args "")

-- Convenience
runClafer :: ClaferArgs -> ClaferM a -> Either ClaferErr a
runClafer args = runIdentity . runClaferT args

-- Add a new fragment to the model. Fragments should be added in order.
addModuleFragment :: Monad m => InputModel -> ClaferT m ()
addModuleFragment input =
  do
    env <- getEnv
    let model' = model env ++ input
    let frags' = frags env ++ [(endPos model')]
    putEnv env{ model = model', frags = frags' }
  where
  endPos "" = Pos 0 0
  endPos model =
    Pos line column
    where
    input = lines model
    line = toInteger $ length input
    column = 1 + (toInteger $ length $ last input)


-- Converts the Err monad (created by the BNFC parser generator) to ClaferT
liftErr :: Monad m => (String -> ClaferErr) -> Err a -> ClaferT m a
liftErr f (Ok m)  = return m
liftErr f (Bad s) = throwError $ f s

-- Parses the model into AST. Adding more fragments beyond this point will have no effect.
parse :: Monad m => ClaferT m ()
parse =
  do
    env <- getEnv
    let inputTokens = (if not 
                  ((fromJust $ new_layout $ args env) ||
                  (fromJust $ no_layout $ args env))
                then 
                   resolveLayout 
                else 
                   id) 
                $ myLexer $
                (if (not $ fromJust $ no_layout $ args env) &&
                    (fromJust $ new_layout $ args env)
                 then 
                   resLayout 
                 else 
                   id)
                $ model env
    ast <- liftErr ParseErr $ mapModule `fmap` pModule inputTokens
    let env' = env{ cAst = Just ast, astModuleTrace = traceAstModule ast }
    putEnv env'

-- Compiles the AST into IR.    
compile :: Monad m => ClaferT m ()
compile =
  do
    env <- getEnv
    let ir = analyze (args env) $ desugar (ast env)
    let (imodule, _, _) = ir
    putEnv $ env{ cIr = Just ir, irModuleTrace = traceIrModule imodule }

-- Splits the IR into their fragments, and generates the output for each fragment.
-- Might not generate the entire output (for example, Alloy scope and run commands) because
-- they do not belong in fragments.
generateFragments :: Monad m => ClaferT m [String]
generateFragments =
  do
    env <- getEnv
    let (iModule, _, _) = ir env
    let fragElems = fragment (sortBy (comparing range) $ mDecls iModule) (frags env)
    
    -- Assumes output mode is Alloy for now
    
    return $ map (generateFragment $ args env) fragElems
  where
  range (IEClafer IClafer{cinPos = pos}) = pos
  range IEConstraint{cpexp = PExp{inPos = pos}} = pos
  range IEGoal{cpexp = PExp{inPos = pos}} = pos
  
  -- Groups IElements by their fragments.
  --   elems must be sorted by range.
  fragment :: [IElement] -> [Pos] -> [[IElement]]
  fragment [] [] = []
  fragment elems (frag : rest) =
    curFrag : fragment restFrags rest
    where
    (curFrag, restFrags) = span (`beforePos` frag) elems
  fragment _ [] = error $ "Unexpected fragment." -- Should not happen. Bug.
  
  beforePos elem pos =
    case range elem of
      Span _ e -> e <= pos
      
  generateFragment :: ClaferArgs -> [IElement] -> String
  generateFragment args frag =
    flatten $ cconcat $ map (genDeclaration args) frag

-- Splits the AST into their fragments, and generates the output for each fragment.
generateHtml :: Monad m => ClaferT m CompilerResult
generateHtml =
  do
    env <- getEnv
    let PosModule _ decls = ast env
    let irMap = irModuleTrace env
    let (iModule, genv, au) = ir env
    return $ CompilerResult { extension = "html", 
                              outputCode = unlines $ generateFragments decls (frags env) irMap,
                              statistics = showStats au $ statsModule iModule,
                              mappingToAlloy = Nothing } 

  where
    line (PosElementDecl (Span pos _) _) = pos
    line (PosEnumDecl (Span pos _) _  _) = pos
    line _                               = Pos 0 0

    generateFragments :: [Declaration] -> [Pos] -> Map Span [Ir] -> [String]
    generateFragments []           _            _     = []
    generateFragments (decl:decls) []           irMap = (cleanOutput $ revertLayout $ printDeclaration decl 0 irMap True) : generateFragments decls [] irMap
    generateFragments (decl:decls) (frag:frags) irMap = if line decl < frag
                                                        then (cleanOutput $ revertLayout $ printDeclaration decl 0 irMap True) : generateFragments decls (frag:frags) irMap
                                                        else "<!-- # FRAGMENT -->" : generateFragments (decl:decls) frags irMap
-- Generates output for the IR.
generate :: Monad m => ClaferT m CompilerResult
generate =
  do
    env <- getEnv
    let cargs = args env
    let (iModule, genv, au) = ir env
    let stats = showStats au $ statsModule iModule
    let (ext, code, mapToAlloy) = case (fromJust $ mode cargs) of
                        Alloy   -> do
                                     let alloyCode = genModule cargs (astrModule iModule, genv)
                                     let addCommentStats = if fromJust $ no_stats cargs then const else addStats
                                     let m = show $ snd alloyCode
                                     ("als", addCommentStats (fst alloyCode) stats, Just m)
                        Alloy42 -> do
                                     let alloyCode = genModule cargs (astrModule iModule, genv)
                                     let addCommentStats = if fromJust $ no_stats cargs then const else addStats
                                     let m = show $ snd alloyCode
                                     ("als", addCommentStats (fst alloyCode) stats, Just m)
                        Xml     -> ("xml", genXmlModule iModule, Nothing)
                        Clafer  -> ("des.cfr", printTree $ sugarModule iModule, Nothing)
                        Html    -> let output = (if (fromJust $ self_contained cargs)
                                              then Css.header ++ Css.css ++ "</head>\n<body>\n"
                                              else "") ++ genHtml (ast env) iModule
                                   in ("html", output, Nothing)
                        Graph   -> ("dot", genGraph (ast env) iModule (dropExtension $ file cargs), Nothing)
    return $ CompilerResult { extension = ext, 
                     outputCode = code, 
                     statistics = stats, 
                     mappingToAlloy = mapToAlloy }
    
data CompilerResult = CompilerResult {
                            extension :: String, 
                            outputCode :: String, 
                            statistics :: String, 
                            mappingToAlloy :: Maybe String 
                            } deriving Show

{-generateHtml :: Monad m => ClaferT m CompilerResult
generateHtml = do
    env <- getEnv
    let (iModule, genv, au) = ir env
    let tree = ast env
    return $ CompilerResult { extension = "html",
                              outputCode = genHtml tree iModule,
                              statistics = showStats au $ statsModule iModule,
                              mappingToAlloy = Nothing }
                              
generateText :: Monad m => ClaferT m CompilerResult
generateText = do
    env <- getEnv
    let (iModule, genv, au) = ir env
    let tree = ast env
    return $ CompilerResult { extension = "txt",
                              outputCode = genText tree iModule,
                              statistics = showStats au $ statsModule iModule,
                              mappingToAlloy = Nothing }

generateGraph :: Monad m => String -> ClaferT m CompilerResult
generateGraph name = do
    env <- getEnv
    let (iModule, genv, au) = ir env
    let tree = ast env
    return $ CompilerResult { extension = "dot",
                              outputCode = genGraph tree iModule name,
                              statistics = showStats au $ statsModule iModule,
                              mappingToAlloy = Nothing }-}

desugar :: Module -> IModule  
desugar tree = desugarModule tree

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
