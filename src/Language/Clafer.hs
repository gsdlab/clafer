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
                        emptyEnv,
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
                        takeSnapShot,
                        SnapShots,
                        emptySnapShots,
                        ir,
                        ast,
                        makeEnv,
                        Pos(..),
                        IrTrace(..),
                        module Language.Clafer.ClaferArgs,
                        module Language.Clafer.Front.ErrM,
                                       
) where

import Data.Either
import Data.List
import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Ord
import Control.Monad
import System.FilePath (dropExtension,takeBaseName)

import Language.ClaferT
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

t a b =
  runClafer defaultClaferArgs $
    do
      addModuleFragment a
      addModuleFragment b
      parse
      compile
      generateFragments

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
 - Use "throwErr" to halt execution:
 -  runClafer args $
 -    when (notValid args) $ throwErr (ClaferErr "Invalid arguments.")
 -
 - Use "catchErrs" to catch the errors.
 -}

-- Add a new fragment to the model. Fragments should be added in order.
addModuleFragment :: Monad m => InputModel -> ClaferT m ()
addModuleFragment input =
  do
    env <- getEnv
    let modelFrags' = modelFrags env ++ [input]
    let frags' = frags env ++ [(endPos $ concat modelFrags')]
    putEnv env{ modelFrags = modelFrags', frags = frags' }
  where
  endPos "" = Pos 1 1
  endPos model =
    Pos line column
    where
    input = lines model
    line = toInteger $ length input
    column = 1 + (toInteger $ length $ last input)
    -- Can't use the builtin lines because it ignores the last empty lines (as of base 4.5).
    lines "" = [""]
    lines input =
      line : rest'
      where
      (line, rest) = break (== '\n') input
      rest' =
        case rest of
          "" -> []
          ('\n' : r) -> lines r
          x -> error $ "linesing " ++ x -- How can it be nonempty and not start with a newline after the break? Should never happen.
      
-- Converts the Err monads (created by the BNFC parser generator) to ClaferT
liftParseErrs :: Monad m => [Err a] -> ClaferT m [a]
liftParseErrs e =
  do
    env <- getEnv
    result <- zipWithM extract [0..] e
    case partitionEithers result of
      ([], ok) -> return ok
      (e',  _) -> throwErrs e'
  where
  extract _ (Ok m)  = return $ Right m
  extract fragId (Bad p s) =
    do
      -- Bad maps to ParseErr
      return $ Left $ ParseErr (ErrFragPos fragId p) s

-- Converts one Err. liftParseErrs is better if you want to report multiple errors. This method will only report
-- one before ceasing execution.
liftParseErr :: Monad m => Err a -> ClaferT m a
liftParseErr e = head `liftM` liftParseErrs [e]


-- Parses the model into AST. Adding more fragments beyond this point will have no effect.
parse :: Monad m => ClaferT m ()
parse =
  do
    env <- getEnv
    let astsErr = map (parseFrag $ args env) $ modelFrags env
    asts <- liftParseErrs astsErr

    -- We need to somehow combine all the ASTS together into a complete AST
    -- However, the source positions inside the ASTs are relative to their
    -- fragments.
    --
    -- For example
    --   Frag1: "A\nB\n"
    --   Frag2: "C\n"
    -- The "C" clafer in Frag2 has position (1, 1) because it is at the start of the fragment.
    -- However, it should have position (3, 1) since that is its position in the complete model.
    --
    -- We can
    --   1. Traverse the model and update the positions so that they are relative to model rather
    --      than the fragment.
    --   2. Reparse the model as a complete model rather in fragments.
    --
    -- The second one is easier so that's we'll do for now. There shouldn't be any errors since
    -- each individual fragment already passed.
    ast' <- case asts of
      -- Special case: if there is only one fragment, then the complete model is contained within it.
      -- Don't need to reparse. This is the common case.
      [oneFrag] -> return oneFrag
      _ -> do
        -- Combine all the fragment syntaxes
        let completeModel = concat $ modelFrags env
        let completeAst = (parseFrag $ args env) completeModel
        liftParseErr completeAst

    
    let ast = mapModule ast'
    let env' = env{ cAst = Just ast, astModuleTrace = traceAstModule ast }
    putEnv env'
    --let debug' = debug $ args env
    --env' <- getEnv
    --when (fromJust debug') $ takeSnapShot env "Parsed"
  where
  parseFrag args =
    pModule .
    (if not 
      ((fromJust $ new_layout args) ||
      (fromJust $ no_layout args))
    then 
       resolveLayout 
    else 
       id) 
    . myLexer .
    (if (not $ fromJust $ no_layout args) &&
        (fromJust $ new_layout args)
     then 
       resLayout 
     else 
       id)

-- Compiles the AST into IR.    
compile :: Monad m => ClaferT m ()
compile =
  do
    env <- getEnv
    ir <- analyze (args env) $ desugar (ast env)
    let (imodule, _, _) = ir
    putEnv $ env{ cIr = Just ir, irModuleTrace = traceIrModule imodule }
    --let debug' = debug $ args env
    --env' <- getEnv
    --when (fromJust debug') $ takeSnapShot "Compiled" env'

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
      PosSpan _ _ e -> e <= pos
  generateFragment :: ClaferArgs -> [IElement] -> String
  generateFragment args frag =
    flatten $ cconcat $ map (genDeclaration args) frag

-- Splits the AST into their fragments, and generates the output for each fragment.
generateHtml env =
    let PosModule _ decls = ast env;
        cargs = args env;
        irMap = irModuleTrace env;
        comments = if fromJust $ add_comments cargs then getComments $ unlines $ modelFrags env else [];
        (iModule, genv, au) = ir env;
    in (if (fromJust $ self_contained cargs) then Css.header ++ "<style>" ++ Css.css ++ "</style></head>\n<body>\n" else "")
       ++ (unlines $ generateFragments decls (frags env) irMap comments) ++
       (if (fromJust $ self_contained cargs) then "</body>\n</html>" else "")

  where
    line (PosElementDecl (Span pos _) _) = pos
    line (PosEnumDecl (Span pos _) _  _) = pos
    line _                               = Pos 0 0
    generateFragments :: [Declaration] -> [Pos] -> Map Span [Ir] -> [(Span, String)] -> [String]
    generateFragments []           _            _     comments = printComments comments
    generateFragments (decl:decls) []           irMap comments = let (comments', c) = printPreComment (range decl) comments in
                                                                   [c] ++ (cleanOutput $ revertLayout $ printDeclaration decl 0 irMap True $ inDecl decl comments') : (generateFragments decls [] irMap $ afterDecl decl comments)
    generateFragments (decl:decls) (frag:frags) irMap comments = if line decl < frag
                                                                 then let (comments', c) = printPreComment (range decl) comments in
                                                                   [c] ++ (cleanOutput $ revertLayout $ printDeclaration decl 0 irMap True $ inDecl decl comments') : (generateFragments decls (frag:frags) irMap $ afterDecl decl comments)
                                                                 else "<!-- # FRAGMENT /-->" : generateFragments (decl:decls) frags irMap comments
    inDecl :: Declaration -> [(Span, String)] -> [(Span, String)]
    inDecl decl comments = let span = range decl in dropWhile (\x -> fst x < span) comments
    afterDecl :: Declaration -> [(Span, String)] -> [(Span, String)]
    afterDecl decl comments = let (Span _ (Pos line _)) = range decl in dropWhile (\(x, _) -> let (Span _ (Pos line' _)) = x in line' <= line) comments
    range (EnumDecl _ _) = noSpan
    range (PosEnumDecl span _ _) = span
    range (ElementDecl _) = noSpan
    range (PosElementDecl span _) = span
    printComments [] = []
    printComments ((span, comment):cs) = (snd (printComment span [(span, comment)]) ++ "<br>\n"):printComments cs

-- Generates output for the IR.
generate :: Monad m => ClaferT m CompilerResult
generate =
  do
    env <- getEnv
    let cargs = args env
    let (iModule, genv, au) = ir env
    let stats = showStats au $ statsModule iModule
    let (ext, code, mapToAlloy) = case (fromJust $ mode cargs) of
                        Alloy   ->  do
                                      let alloyCode = genModule cargs (astrModule iModule, genv)
                                      let addCommentStats = if fromJust $ no_stats cargs then const else addStats
                                      let m = snd alloyCode
                                      ("als", addCommentStats (fst alloyCode) stats, Just m)
                        Alloy42  -> do
                                      let alloyCode = genModule cargs (astrModule iModule, genv)
                                      let addCommentStats = if fromJust $ no_stats cargs then const else addStats
                                      let m = snd alloyCode
                                      ("als", addCommentStats (fst alloyCode) stats, Just m)
                        Xml      -> ("xml", genXmlModule iModule, Nothing)
                        Clafer   -> ("des.cfr", printTree $ sugarModule iModule, Nothing)
                        Html     -> ("html", generateHtml env, Nothing)
                        Graph    -> ("dot", genSimpleGraph (ast env) iModule (takeBaseName $ file cargs) (fromJust $ show_references cargs), Nothing)
                        CVLGraph -> ("dot", genCVLGraph (ast env) iModule (takeBaseName $ file cargs), Nothing)
    return $ CompilerResult { extension = ext, 
                     outputCode = code, 
                     statistics = stats,
                     claferEnv  = env,
                     mappingToAlloy = fromMaybe [] mapToAlloy }
    
data CompilerResult = CompilerResult {
                            extension :: String, 
                            outputCode :: String, 
                            statistics :: String,
                            claferEnv :: ClaferEnv,
                            mappingToAlloy :: [(Span, IrTrace)] -- Maps source constraint spans in Alloy to the spans in the IR
                            } deriving Show

desugar :: Module -> IModule  
desugar tree = desugarModule tree

liftError :: (Monad m, Language.ClaferT.Throwable t) => Either t a -> ClaferT m a
liftError = either throwErr return

analyze :: Monad m => ClaferArgs -> IModule -> ClaferT m (IModule, GEnv, Bool)
analyze args tree = do
  let dTree' = findDupModule args tree
  let au = allUnique dTree'
  let args' = args{skip_resolver = Just $ au && (fromJust $ skip_resolver args)}
  (rTree, genv) <- liftError $ resolveModule args' dTree'
  let tTree = transModule rTree
  return (optimizeModule args' (tTree, genv), genv, au)

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
