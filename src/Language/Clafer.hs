{-
 Copyright (C) 2012-2014 Kacper Bak, Jimmy Liang, Michal Antkiewicz <http://gsd.uwaterloo.ca>

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
{- | Top-level interface to the Clafer compiler

Normal usage:

> t :: InputModel -> InputModel -> Either [ClaferErr] [String]
> t a b =
>   runClafer defaultClaferArgs $
>     do
>       addModuleFragment a
>       addModuleFragment b
>       parse
>       compile
>       generateFragments

Example of compiling a model consisting of one fragment:

> compileOneFragment :: ClaferArgs -> InputModel -> Either ClaferErr CompilerResult
> compileOneFragment args model =
>   runClafer args $
>     do
>       addModuleFragment model
>       parse
>       compile
>       generate

Use "generateFragments" instead to generate output based on their fragments.

> compileTwoFragments :: ClaferArgs -> InputModel -> InputModel -> Either ClaferErr [String]
> compileTwoFragments args frag1 frag2 =
>   runClafer args $
>    do
>      addModuleFragment frag1
>      addModuleFragment frag2
>      parse
>      compile
>      generateFragments

Use "throwErr" to halt execution:

> runClafer args $
>   when (notValid args) $ throwErr (ClaferErr "Invalid arguments.")

Use "catchErrs" to catch the errors.
-}
module Language.Clafer (addModuleFragment,
                        compile,
                        parse,
                        generate,
                        generateHtml,
                        generateFragments,
                        runClaferT,
                        runClafer,
                        ClaferErr,
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
                        getIr,
                        getAst,
                        makeEnv,
                        Pos(..),
                        IrTrace(..),
                        module Language.Clafer.ClaferArgs,
                        module Language.Clafer.Front.ErrM)
where

import Data.Data.Lens
import Data.Either
import Data.List
import Data.Maybe
import qualified Data.Map as Map
import Data.Ord
import Control.Monad
import Control.Lens.Plated
import System.FilePath (takeBaseName)

import Language.ClaferT 
import Language.Clafer.Common
import Language.Clafer.Front.ErrM
import Language.Clafer.ClaferArgs hiding (Clafer)
import qualified Language.Clafer.ClaferArgs as Mode (ClaferMode (Clafer))
import Language.Clafer.Comments
import qualified Language.Clafer.Css as Css
import Language.Clafer.Front.Lexclafer
import Language.Clafer.Front.Parclafer
import Language.Clafer.Front.Printclafer
import Language.Clafer.Front.Absclafer 
import Language.Clafer.Front.LayoutResolver
import Language.Clafer.Intermediate.Tracing
import Language.Clafer.Intermediate.Intclafer
import Language.Clafer.Intermediate.Desugarer
import Language.Clafer.Intermediate.Resolver
import Language.Clafer.Intermediate.StringAnalyzer
import Language.Clafer.Intermediate.Transformer
import Language.Clafer.Intermediate.ScopeAnalysis
import Language.Clafer.Optimizer.Optimizer
import Language.Clafer.Generator.Alloy
import Language.Clafer.Generator.Choco
import Language.Clafer.Generator.Xml
import Language.Clafer.Generator.Python
import Language.Clafer.Generator.Schema
import Language.Clafer.Generator.Stats
import Language.Clafer.Generator.Html
import Language.Clafer.Generator.Graph

type VerbosityL = Int
type InputModel = String

-- | Add a new fragment to the model. Fragments should be added in order.
addModuleFragment :: Monad m => InputModel -> ClaferT m ()
addModuleFragment i =
  do
    env <- getEnv
    let modelFrags' = modelFrags env ++ [i]
    let frags' = frags env ++ [(endPos $ concat modelFrags')]
    putEnv env{ modelFrags = modelFrags', frags = frags' }
  where
  endPos "" = Pos 1 1
  endPos model =
    Pos line' column'
    where
    input' = lines' model
    line' = toInteger $ length input'
    column' = 1 + (toInteger $ length $ last input')
    -- Can't use the builtin lines because it ignores the last empty lines (as of base 4.5).
    lines' "" = [""]
    lines' input'' =
      line'' : rest'
      where
      (line'', rest) = break (== '\n') input''
      rest' =
        case rest of
          "" -> []
          ('\n' : r) -> lines' r
          x -> error $ "linesing " ++ x -- How can it be nonempty and not start with a newline after the break? Should never happen.
      
-- | Converts the Err monads (created by the BNFC parser generator) to ClaferT
liftParseErrs :: Monad m => [Err a] -> ClaferT m [a]
liftParseErrs e =
  do
    result <- zipWithM extract [0..] e
    case partitionEithers result of
      ([], ok) -> return ok
      (e',  _) -> throwErrs e'
  where
  extract _ (Ok m)  = return $ Right m
  extract frgId (Bad p s) =
    do
      -- Bad maps to ParseErr
      return $ Left $ ParseErr (ErrFragPos frgId p) s

-- | Converts one Err. liftParseErrs is better if you want to report multiple errors. 
-- | This method will only report one before ceasing execution.
liftParseErr :: Monad m => Err a -> ClaferT m a
liftParseErr e = head `liftM` liftParseErrs [e]


-- | Parses the model into AST. Adding more fragments beyond this point will have no effect.
parse :: Monad m => ClaferT m ()
parse =
  do
    env <- getEnv
    astsErr <- mapM (parseFrag $ args env) $ modelFrags env
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
    ast <- case asts of
      -- Special case: if there is only one fragment, then the complete model is contained within it.
      -- Don't need to reparse. This is the common case.
      [oneFrag] -> return oneFrag
      _ -> do
        -- Combine all the fragment syntaxes
        let completeModel = concat $ modelFrags env
        completeAst <- (parseFrag $ args env) completeModel
        liftParseErr completeAst

    let env' = env{ cAst = Just ast, astModuleTrace = traceAstModule ast }
    putEnv env'
  where
  parseFrag :: (Monad m) => ClaferArgs -> String -> ClaferT m (Err Module)
  parseFrag args' =
    (>>= (return . pModule)) .
    (if not 
      ((new_layout args') ||
      (no_layout args'))
    then 
       resolveLayout 
    else 
       return) 
    . myLexer .
    (if (not $ no_layout args') &&
        (new_layout args')
     then 
       resLayout 
     else 
       id)

-- | Compiles the AST into IR.    
compile :: Monad m => ClaferT m ()
compile =
  do
    env <- getEnv
    ast' <- getAst
    let desugaredMod = desugar ast'
    let clafersWithKeyWords = foldMapIR isKeyWord desugaredMod
    when (""/=clafersWithKeyWords) $ throwErr (ClaferErr $ ("The model contains clafers with keywords as names in the following places:\n"++) $ clafersWithKeyWords :: CErr Span)
    ir <- analyze (args env) desugaredMod
    let (imodule, _, _) = ir

    let spanList = foldMapIR gt1 imodule
    when ((afm $ args env) && spanList/="") $ throwErr (ClaferErr $ ("The model is not an attributed feature model.\nThe following places contain cardinality larger than 1:\n"++) $ spanList :: CErr Span)
    putEnv $ env{ cIr = Just ir, irModuleTrace = traceIrModule imodule }
    where
      isKeyWord :: Ir -> String
      isKeyWord (IRClafer IClafer{_cinPos = (Span (Pos l c) _) ,_ident=i}) = if (i `elem` keyWords) then ("Line " ++ show l ++ " column " ++ show c ++ "\n") else ""
      isKeyWord _ = ""
      gt1 :: Ir -> String
      gt1 (IRClafer (IClafer (Span (Pos l c) _) False _ _ _ _ (Just (_, m)) _ _ _)) = if (m > 1 || m < 0) then ("Line " ++ show l ++ " column " ++ show c ++ "\n") else ""
      gt1 _ = ""

-- | Splits the IR into their fragments, and generates the output for each fragment.
-- | Might not generate the entire output (for example, Alloy scope and run commands) because
-- | they do not belong in fragments.
generateFragments :: Monad m => ClaferT m [String]
generateFragments =
  do
    env <- getEnv
    (iModule, _, _) <- getIr
    fragElems <- fragment (sortBy (comparing rnge) $ _mDecls iModule) (frags env)
    
    -- Assumes output mode is Alloy for now
    
    return $ map (generateFragment $ args env) fragElems
  where
  rnge (IEClafer IClafer{_cinPos = p}) = p
  rnge IEConstraint{_cpexp = PExp{_inPos = p}} = p
  rnge IEGoal{_cpexp = PExp{_inPos = p}} = p
  
  -- Groups IElements by their fragments.
  --   elems must be sorted by range.
  fragment :: (Monad m) => [IElement] -> [Pos] -> ClaferT m [[IElement]]
  fragment [] [] = return []
  fragment elems (frag : rest) =
    fragment restFrags rest >>= return . (curFrag:)
    where
    (curFrag, restFrags) = span (`beforePos` frag) elems
  fragment _ [] = throwErr $ (ClaferErr $ "Unexpected fragment." :: CErr Span) -- Should not happen. Bug.
  
  beforePos ele p =
    case rnge ele of
      Span _ e -> e <= p
  generateFragment :: ClaferArgs -> [IElement] -> String
  generateFragment args' frag =
    flatten $ cconcat $ map (genDeclaration args') frag

-- | Splits the AST into their fragments, and generates the output for each fragment.
generateHtml :: ClaferEnv -> Module -> String
generateHtml env ast' =
    let Module _ decls' = ast';
        cargs = args env;
        irMap = irModuleTrace env;
        comments = if add_comments cargs then getComments $ unlines $ modelFrags env else [];
    in (if (self_contained cargs) then Css.header ++ "<style>" ++ Css.css ++ "</style></head>\n<body>\n" else "")
       ++ (unlines $ genFragments decls' (frags env) irMap comments) ++
       (if (self_contained cargs) then "</body>\n</html>" else "")

  where
    lne :: Declaration -> Pos
    lne (ElementDecl (Span p _) _) = p
    lne (EnumDecl (Span p _) _  _) = p
    lne _                               = Pos 0 0
    genFragments :: [Declaration] -> [Pos] -> Map.Map Span [Ir] -> [(Span, String)] -> [String]
    genFragments []           _            _     comments = printComments comments
    genFragments (decl:decls') []           irMap comments = let (comments', c) = printPreComment (getSpan decl) comments in
                                                                   [c] ++ (cleanOutput $ revertLayout $ printDeclaration decl 0 irMap True $ inDecl decl comments') : (genFragments decls' [] irMap $ afterDecl decl comments)
    genFragments (decl:decls') (frg:frgs) irMap comments = if lne decl < frg
                                                                 then let (comments', c) = printPreComment (getSpan decl) comments in
                                                                   [c] ++ (cleanOutput $ revertLayout $ printDeclaration decl 0 irMap True $ inDecl decl comments') : (genFragments decls' (frg:frgs) irMap $ afterDecl decl comments)
                                                                 else "<!-- # FRAGMENT /-->" : genFragments (decl:decls') frgs irMap comments
    inDecl :: Declaration -> [(Span, String)] -> [(Span, String)]
    inDecl decl comments = let s = getSpan decl in dropWhile (\x -> fst x < s) comments
    afterDecl :: Declaration -> [(Span, String)] -> [(Span, String)]
    afterDecl decl comments = let (Span _ (Pos line' _)) = getSpan decl in dropWhile (\(x, _) -> let (Span _ (Pos line'' _)) = x in line'' <= line') comments
    printComments [] = []
    printComments ((s, comment):cs) = (snd (printComment s [(s, comment)]) ++ "<br>\n"):printComments cs

noReals :: IModule -> Bool
noReals iModule = reals == []
  where 
    iexps :: [ IExp ]
    iexps = universeOn biplate iModule
    reals = filter isIDouble iexps
    isIDouble (IDouble _) = True
    isIDouble _           = False

-- | Generates outputs for the given IR.
generate :: Monad m => ClaferT m (Map.Map ClaferMode CompilerResult)
generate =
  do
    env <- getEnv
    ast' <- getAst
    (iModule, genv, au) <- getIr
    let 
      hasNoReals = noReals iModule
      cargs = args env
      modes = mode cargs
      stats = showStats au $ statsModule iModule
      scopes = getScopeStrategy (scope_strategy cargs) iModule

    return $ Map.fromList ( 
        -- result for Alloy
        (if (Alloy `elem` modes)
          then if (hasNoReals)
                then 
                  let 
                  (imod,strMap) = astrModule iModule
                  alloyCode = genModule cargs{mode = [Alloy]} (imod, genv) scopes
                  addCommentStats = if no_stats cargs then const else addStats 
               in 
                  [ (Alloy, 
                    CompilerResult { 
                       extension = "als41", 
                     outputCode = addCommentStats (fst alloyCode) stats, 
                     statistics = stats,
                     claferEnv  = env,
                     mappingToAlloy = fromMaybe [] (Just $ snd alloyCode),
                     stringMap = strMap,
                     scopesList = scopes
                      })
                    ]
                else [ (Alloy, 
                        NoCompilerResult { 
                         reason = "Alloy output unavailable because the model contains real numbers." 
                    })
                  ]
          else []
        ) 
        ++
        -- result for Alloy42
        (if (Alloy42 `elem` modes)
          then if (hasNoReals)
                then
                   let 
                  (imod,strMap) = astrModule iModule
                  alloyCode = genModule cargs{mode = [Alloy42]} (imod, genv) scopes
                  addCommentStats = if no_stats cargs then const else addStats 
               in 
                  [ (Alloy42, 
                    CompilerResult { 
                         extension = "als", 
                     outputCode = addCommentStats (fst alloyCode) stats, 
                     statistics = stats,
                     claferEnv  = env,
                     mappingToAlloy = fromMaybe [] (Just $ snd alloyCode),
                     stringMap = strMap,
                     scopesList = scopes
                        })
                      ]
                else [ (Alloy, 
                        NoCompilerResult { 
                         reason = "Alloy output unavailable because the model contains real numbers." 
                    })
                  ]
          else []
        )   
        -- result for XML    
        ++ (if (Xml `elem` modes)
          then [ (Xml,
                  CompilerResult { 
                   extension = "xml", 
                   outputCode = genXmlModule iModule, 
                   statistics = stats,
                   claferEnv  = env,
                   mappingToAlloy = [],
                   stringMap = Map.empty,
                   scopesList = []
                  }) ]
          else []
        )
        -- result for Clafer
        ++ (if (Mode.Clafer `elem` modes)
          then [ (Mode.Clafer,
                  CompilerResult { 
                   extension = "des.cfr", 
                   outputCode = printTree $ sugarModule iModule, 
                   statistics = stats,
                   claferEnv  = env,
                   mappingToAlloy = [],
                   stringMap = Map.empty,
                   scopesList = []
                  }) ]
          else []
        )
        -- result for Html    
        ++ (if (Html `elem` modes)
          then [ (Html,
                  CompilerResult { 
                   extension = "html", 
                   outputCode = generateHtml env ast', 
                   statistics = stats,
                   claferEnv  = env,
                   mappingToAlloy = [],
                   stringMap = Map.empty,
                   scopesList = []
                  }) ]
          else []
        )
        ++ (if (Graph `elem` modes)
          then [ (Graph,
                  CompilerResult { 
                     extension = "dot", 
                     outputCode = genSimpleGraph ast' iModule (takeBaseName $ file cargs) (show_references cargs), 
                     statistics = stats,
                     claferEnv  = env,
                     mappingToAlloy = [],
                     stringMap = Map.empty,
                     scopesList = []
                  }) ]
          else []
        )
        ++ (if (CVLGraph `elem` modes)
          then [ (CVLGraph,
                  CompilerResult { 
                       extension = "cvl.dot", 
                       outputCode = genCVLGraph ast' iModule (takeBaseName $ file cargs), 
                       statistics = stats,
                       claferEnv  = env,
                       mappingToAlloy = [],
                       stringMap = Map.empty,
                       scopesList = []
                  }) ]
          else []
        )
        -- result for Python    
        ++ (if (Python `elem` modes)
          then [ (Python, 
                  CompilerResult { 
                   extension = "py", 
                   outputCode = genPythonModule iModule,
                   statistics = stats,
                   claferEnv  = env,
                   mappingToAlloy = [],
                   stringMap = Map.empty,
                   scopesList = scopes
                  }) ]
          else []
        )
        -- result for Choco    
        ++ (if (Choco `elem` modes)
          then let 
                  imod = iModule
               in
                  [ (Choco, 
                     CompilerResult { 
                         extension = "js", 
                         outputCode = genCModule cargs (imod, genv) scopes, 
                         statistics = stats,
                         claferEnv  = env,
                         mappingToAlloy = [],
                         stringMap = Map.empty,
                         scopesList = scopes
                      }) ]
          else []
        ))
    
-- | Result of generation for a given mode
data CompilerResult = CompilerResult {
                            -- | output file extension
                            extension :: String, 
                            -- | output text
                            outputCode :: String, 
                            statistics :: String,
                            -- | the final environment of the compiler
                            claferEnv :: ClaferEnv,
                            -- | Maps source constraint spans in Alloy to the spans in the IR
                            mappingToAlloy :: [(Span, IrTrace)], 
                            -- | Map back from Ints used to represent Strings
                            stringMap :: (Map.Map Int String),
                            -- | scopes generated by scope inference
                            scopesList :: [(UID, Integer)]
                            } 
                      | NoCompilerResult {
                            reason :: String
                            } deriving Show

desugar :: Module -> IModule  
desugar iModule = desugarModule iModule

liftError :: (Monad m, Language.ClaferT.Throwable t) => Either t a -> ClaferT m a
liftError = either throwErr return

analyze :: Monad m => ClaferArgs -> IModule -> ClaferT m (IModule, GEnv, Bool)
analyze args' iModule = do
  liftError $ findDupModule args' iModule
  let 
    au = allUnique iModule
  let args'' = args'{skip_resolver = au && (skip_resolver args')}
  (rTree, genv) <- liftError $ resolveModule args'' iModule
  let tTree = transModule rTree
  return (optimizeModule args'' (tTree, genv), genv, au)

addStats :: String -> String -> String
addStats code stats = "/*\n" ++ stats ++ "*/\n" ++ code

showStats :: Bool -> Stats -> String
showStats au (Stats na nr nc nconst ngoals sgl) =
  unlines [ "All clafers: " ++ (show (na + nr + nc)) ++ " | Abstract: " ++ (show na) ++ " | Concrete: " ++ (show nc) ++ " | References: " ++ (show nr)
          , "Constraints: " ++ show nconst
          , "Goals: " ++ show ngoals  
          , "Global scope: " ++ showInterval sgl
          , "Can skip resolver: " ++ if au then "yes" else "no" ]

showInterval :: (Integer, Integer) -> String
showInterval (n, -1) = show n ++ "..*"
showInterval (n, m) = show n ++ ".." ++ show m

-- | The XML Schema of the IR
claferIRXSD :: String
claferIRXSD = Language.Clafer.Generator.Schema.xsd

-- | reserved keywords
keyWords :: [String]
keyWords = ["ref","parent","abstract", "else", "in", "no", "opt", "xor", "all", "enum", "lone", "not", "or", "disj", "extends", "mux", "one", "some"]