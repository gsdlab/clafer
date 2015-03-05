{-# LANGUAGE DeriveDataTypeable, NamedFieldPuns #-}
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
>       generate

Example of compiling a model consisting of one fragment:

> compileOneFragment :: ClaferArgs -> InputModel -> Either ClaferErr CompilerResult
> compileOneFragment args model =
>   runClafer args $
>     do
>       addModuleFragment model
>       parse
>       compile
>       generate

> compileTwoFragments :: ClaferArgs -> InputModel -> InputModel -> Either ClaferErr [String]
> compileTwoFragments args frag1 frag2 =
>   runClafer args $
>    do
>      addModuleFragment frag1
>      addModuleFragment frag2
>      parse
>      compile
>      generate

Use "throwErr" to halt execution:

> runClafer args $
>   when (notValid args) $ throwErr (ClaferErr "Invalid arguments.")

Use "catchErrs" to catch the errors.
-}
module Language.Clafer (runCompiler,
                        addModuleFragment,
                        compile,
                        parse,
                        desugar,
                        generate,
                        generateHtml,
                        runClaferT,
                        runClafer,
                        ClaferErr,
                        getEnv,
                        putEnv,
                        CompilerResult(..),
                        claferIRXSD,
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
import Control.Monad
import Control.Monad.State
import Control.Lens.Plated
import System.Exit
import System.FilePath (dropExtension,takeBaseName,takeFileName)
import System.Process (readProcessWithExitCode, system)

import Language.ClaferT
import Language.Clafer.Common
import Language.Clafer.Front.ErrM
import Language.Clafer.ClaferArgs hiding (Clafer)
import qualified Language.Clafer.ClaferArgs as Mode (ClaferMode (Clafer))
import Language.Clafer.Comments
import qualified Language.Clafer.Css as Css
import Language.Clafer.Front.LexClafer
import Language.Clafer.Front.ParClafer
import Language.Clafer.Front.PrintClafer
import Language.Clafer.Front.AbsClafer
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
import Language.Clafer.Generator.Concat
import Language.Clafer.Generator.Xml
import Language.Clafer.Generator.Python
import Language.Clafer.Generator.Schema
import Language.Clafer.Generator.Stats
import Language.Clafer.Generator.Html
import Language.Clafer.Generator.Graph
import Language.Clafer.JSONMetaData
import Language.Clafer.QNameUID

type InputModel = String

-- | Run the Clafer compiler.
-- mURL = Nothing means compile the top-level module
-- mURL = Just url means compile an imported module from the given url
runCompiler :: Maybe URL -> ClaferArgs -> InputModel -> IO (Either [ClaferErr] (Map.Map ClaferMode CompilerResult))
runCompiler    mURL         args'         inputModel =
  do
    result <- runClaferT args' $
      do
        forM_ (fragments inputModel) addModuleFragment
        parse
        iModule <- desugar mURL
        -- need to runCompiler on imports
        importedResultMaps <- liftIO $ do
          forM (_mModules iModule) $ \url -> do
            -- use the same args just change the file name
            importedModel <- retrieveModelFromURL url
            runCompiler (Just url) (args' { file = getFileName url }) importedModel
        // TODO: add ClaferEnvs from importedResultMaps to this ClaferEnv
        compile iModule
        resultsMap <- generate
        fs <- save args' resultsMap
        when (validate args') $ forM_ fs (liftIO . runValidate args' )
        return resultsMap
    _ <- if Html `elem` (mode args')
      then htmlCatch result args' inputModel
      else return ()
    result `cth` handleErrs
    return result
  where
  getFileName :: URL                         -> FilePath
  getFileName ('f':'i':'l':'e':':':'/':'/':n) = takeFileName n
  getFileName ('h':'t':'t':'p':':':'/':'/':n) = takeFileName n
  getFileName ('f':'t':'p':':':'/':'/':n)     = takeFileName n
  getFileName n                               = n
  cth (Left err) f = f err
  cth (Right r)  _ = return ()
  fragments model = map unlines $ fragments' $ lines model
  fragments' []                  = []
  fragments' ("//# FRAGMENT":xs) = fragments' xs
  fragments' model               = takeWhile (/= "//# FRAGMENT") model : fragments' (dropWhile (/= "//# FRAGMENT") model)
--  htmlCatch :: Either ClaferErr CompilerResult -> ClaferArgs -> String -> IO(CompilerResult)
  htmlCatch (Right r) _ _ = return ()
  htmlCatch (Left err) args'' model =
    do let f = (dropExtension $ file args'') ++ ".html"
       let result = (if (self_contained args'')
                     then Css.header ++ "<style>" ++ Css.css ++ "</style>" ++ "</head>\n<body>\n<pre>\n"
                     else "")
                     ++ highlightErrors model err ++
                     (if (self_contained args'')
                      then "\n</pre>\n</html>"
                      else "")
       liftIO $ if console_output args'' then putStrLn result else writeFile f result

  handleErrs = mapM_ handleErr

  handleErr (ClaferErr mesg) =
    do
      putStrLn "\nError...\n"
      putStrLn mesg
      exitFailure
  -- We only use one fragment. Fragment id and position is not useful to us. We
  -- only care about the position relative to
  handleErr (ParseErr ErrPos{modelPos = Pos l c} mesg) =
    do
      putStrLn $ "\nParse failed at line " ++ show l ++ " column " ++ show c ++ "..."
      putStrLn mesg
      exitFailure
  handleErr (SemanticErr ErrPos{modelPos = Pos l c} mesg) =
    do
      putStrLn $ "\nCompile error at line " ++ show l ++ " column " ++ show c ++ "..."
      putStrLn mesg
      exitFailure

save :: MonadIO m => ClaferArgs -> (Map.Map ClaferMode CompilerResult) -> ClaferT m [ String ]
save args' resultsMap =
  do
    let results = snd $ unzip $ Map.toList resultsMap
    -- print stats only once
    when (not $ no_stats args') $ liftIO $ printStats results
    -- save the outputs
    (iModule, _, _) <- getIr
    forM results $ saveResult iModule resultsMap
  where
    -- saveResult :: MonadIO m => CompilerResult -> IModule -> (Map.Map ClaferMode CompilerResult) -> ClaferT m String
    saveResult iModule' resultsMap' result@CompilerResult { extension } = do
      result' <- if (add_graph args') && (Html `elem` (mode args') && ("dot" `isSuffixOf` (extension)))
            then do
                   ast' <- getAst
                   (_, graph, _) <- liftIO $ readProcessWithExitCode "dot"  ["-Tsvg"] $ genSimpleGraph ast' iModule' (takeBaseName $ file args') (show_references args')
                   return $ summary graph result
            else return result
      let f = dropExtension $ file args'
      let f' = f ++ "." ++ extension
      liftIO $ if console_output args' then putStrLn (outputCode result') else writeFile f' (outputCode result')
      liftIO $ when (alloy_mapping args') $ writeFile (f ++ ".map") $ show (mappingToAlloy result')
      let
        qNameMaps :: QNameMaps
        qNameMaps = deriveQNameMaps iModule'
      liftIO $ when (meta_data args') $ writeFile (f ++ ".cfr-map") $ generateJSONnameUIDMap qNameMaps
      liftIO $ when (meta_data args' && inScopeModes) $ writeFile (f ++ ".cfr-scope") $ generateJSONScopes qNameMaps $ getScopesList resultsMap'
      return f'
    saveResult _ _ NoCompilerResult { reason } = do
      liftIO $ putStrLn reason
      return ""
    printStats :: [CompilerResult] -> IO ()
    printStats []         = putStrLn "No compiler output."
    printStats (r:rs) = case r of
      CompilerResult { statistics } -> putStrLn statistics
      (NoCompilerResult _) -> printStats rs

    inScopeModes :: Bool
    inScopeModes =
      Alloy `elem` mode args' ||
      Alloy42 `elem` mode args' ||
      Choco `elem` mode args'

    getScopesList :: (Map.Map ClaferMode CompilerResult) -> [(UID, Integer)]
    getScopesList    resultsMap =
        let
           alloyResult = Map.lookup Alloy resultsMap
           alloy42Result = Map.lookup Alloy42 resultsMap
           chocoResult = Map.lookup Choco resultsMap
        in
           if (isNothing alloyResult)
           then if (isNothing alloy42Result)
                then if (isNothing chocoResult)
                     then []
                     else scopesList $ fromJust chocoResult
                else scopesList $ fromJust alloy42Result
           else scopesList $ fromJust alloyResult

summary :: String -> CompilerResult -> CompilerResult
summary graph result = result{outputCode=unlines $ summary' graph ("<pre>" ++ statistics result ++ "</pre>") (lines $ outputCode result)}

summary' :: String -> String -> [String] -> [String]
summary' _ _ [] = []
summary' graph stats ("<!-- # SUMMARY /-->":xs) = graph:stats:summary' graph stats xs
summary' graph stats ("<!-- # STATS /-->":xs) = stats:summary' graph stats xs
summary' graph stats ("<!-- # GRAPH /-->":xs) = graph:summary' graph stats xs
summary' graph stats ("<!-- # CVLGRAPH /-->":xs) = graph:summary' graph stats xs
summary' graph stats (x:xs) = x:summary' graph stats xs

runValidate :: ClaferArgs -> String -> IO ()
runValidate args' fo = do
  let path = (tooldir args') ++ "/"
  liftIO $ putStrLn ("Validating '" ++ fo ++"'")
  let modes = mode args'
  when (Xml `elem` modes && "xml" `isSuffixOf` fo) $ do
      writeFile "ClaferIR.xsd" claferIRXSD
      voidf $ system $ "java -classpath " ++ path ++ " XsdCheck ClaferIR.xsd " ++ fo
  when (Alloy `elem` modes && "als41" `isSuffixOf` fo) $ do
    voidf $ system $ validateAlloy path "4" ++ fo
  when (Alloy42 `elem` modes && "als" `isSuffixOf` fo) $ do
    voidf $ system $ validateAlloy path "4.2" ++ fo
  when (Mode.Clafer `elem` modes && "des.cfr" `isSuffixOf` fo) $ do
    voidf $ system $ "../dist/build/clafer/clafer -s -m=clafer " ++ fo

validateAlloy :: String -> String -> String
validateAlloy path version = "java -cp " ++ path ++ "alloy" ++ version ++ ".jar edu.mit.csail.sdg.alloy4whole.ExampleUsingTheCompiler "


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
    putEnv env{ cAst = Just ast, astModuleTrace = traceAstModule ast }
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

desugar :: Monad m => Maybe URL -> ClaferT m IModule
desugar mURL = do
  ast' <- getAst
  return $ desugarModule mURL ast'

-- | Compiles the AST into IR.
compile :: Monad m => IModule -> ClaferT m ()
compile desugaredMod = do
    env <- getEnv
    let clafersWithKeyWords = foldMapIR isKeyWord desugaredMod
    when (""/=clafersWithKeyWords) $ throwErr (ClaferErr $ ("The model contains clafers with keywords as names in the following places:\n"++) $ clafersWithKeyWords :: CErr Span)
    ir <- analyze (args env) desugaredMod
    let (imodule, _, _) = ir

    let spanList = foldMapIR gt1 imodule
    when ((afm $ args env) && spanList/="") $ throwErr (ClaferErr $ ("The model is not an attributed feature model.\nThe following places contain cardinality larger than 1:\n"++) $ spanList :: CErr Span)
    putEnv $ env{ cIr = Just ir }
    where
      isKeyWord :: Ir -> String
      isKeyWord (IRClafer IClafer{_cinPos = (Span (Pos l c) _) ,_ident=i}) = if (i `elem` keywordIdents) then ("Line " ++ show l ++ " column " ++ show c ++ "\n") else ""
      isKeyWord _ = ""
      gt1 :: Ir -> String
      gt1 (IRClafer (IClafer (Span (Pos l c) _) False _ _ _ _ _ _ (Just (_, m)) _ _)) = if (m > 1 || m < 0) then ("Line " ++ show l ++ " column " ++ show c ++ "\n") else ""
      gt1 _ = ""

computeImportsMap :: Monad m => Module -> ClaferT m (Map.Map String IModule)
computeImportsMap ast' = do
  let
    (Module _ imports _) = ast'
    importedIModules = map import2IModule imports
  return $ Map.fromList importedIModules
  where
    import2IModule :: Import -> (String, IModule)
    import2IModule    imp = (url, iModule)
      where
        url = getURL imp
        iModule = IModule url [] []
    getURL (Import _ (PosURL (_, u))) = u

-- | Splits the AST into their fragments, and generates the output for each fragment.
generateHtml :: ClaferEnv -> String
generateHtml env =
    let (Just (Module _ imports' decls')) = cAst env;
        cargs = args env;
        irMap = irModuleTrace env;
        comments = if add_comments cargs then getComments $ unlines $ modelFrags env else [];
    in (if (self_contained cargs) then Css.header ++ "<style>" ++ Css.css ++ "</style></head>\n<body>\n" else "")
       ++ (unlines $ genFragments imports' decls' (frags env) irMap comments) ++
       (if (self_contained cargs) then "</body>\n</html>" else "")

  where
    lne :: Declaration -> Pos
    lne (ElementDecl (Span p _) _) = p
    lne (EnumDecl (Span p _) _  _) = p

    genFragments :: [Import] -> [Declaration] -> [Pos]   -> Map.Map Span [Ir] -> [(Span, String)] -> [String]
    genFragments    []          []               _          _                    comments =
      printComments comments
    genFragments    (imp:imps)  declarations     positions  irMap                comments =
      let
        impSpan = (getSpan imp)
        (comments', c) = printPreComment impSpan comments
      in
        [c]
        ++ (cleanOutput $ printImport True imp $ inSpan impSpan comments')
        : (genFragments imps declarations positions  irMap $ afterSpan impSpan comments')
    genFragments    []          (decl:decls')    []         irMap                comments =
      let
        (comments', c) = printPreComment (getSpan decl) comments
      in
        [c]
        ++ (cleanOutput $ revertLayout $ printDeclaration decl 0 irMap True $ inSpan (getSpan decl) comments')
        : (genFragments [] decls' [] irMap $ afterSpan (getSpan decl) comments)
    genFragments    []          (decl:decls')    (frg:frgs) irMap                comments =
      if lne decl < frg
        then let
               (comments', c) = printPreComment (getSpan decl) comments
             in
               [c]
               ++ (cleanOutput $ revertLayout $ printDeclaration decl 0 irMap True $ inSpan (getSpan decl) comments')
               : (genFragments [] decls' (frg:frgs) irMap $ afterSpan (getSpan decl) comments)
        else "<!-- # FRAGMENT /-->" : genFragments [] (decl:decls') frgs irMap comments
    inSpan :: Span -> [(Span, String)] -> [(Span, String)]
    inSpan s comments = dropWhile (\x -> fst x < s) comments
    afterSpan :: Span -> [(Span, String)] -> [(Span, String)]
    afterSpan (Span _ (Pos line' _)) comments =
      dropWhile (\(x, _) -> let (Span _ (Pos line'' _)) = x in line'' <= line') comments

    printComments [] = []
    printComments ((s, comment):cs) = (snd (printComment s [(s, comment)]) ++ "<br>\n"):printComments cs

iExpBasedChecks :: IModule -> (Bool, Bool)
iExpBasedChecks iModule = (null realLiterals, null productOperators)
  where
    iexps :: [ IExp ]
    iexps = universeOn biplate iModule
    realLiterals = filter isIDouble iexps
    productOperators = filter isProductOperator iexps
    isIDouble (IDouble _) = True
    isIDouble _           = False
    isProductOperator (IFunExp op' _) = op' == iProdSet
    isProductOperator _               = False

iClaferBasedChecks :: IModule -> Bool
iClaferBasedChecks iModule = null $ filter hasReferenceToReal iClafers
  where
    iClafers :: [ IClafer ]
    iClafers = universeOn biplate iModule
    hasReferenceToReal (IClafer{_reference=(Just IReference{_ref=pexp'})}) = (getSuperId pexp') == "real"
    hasReferenceToReal _               = False

-- | Generates outputs for the given IR.
generate :: Monad m => ClaferT m (Map.Map ClaferMode CompilerResult)
generate =
  do
    env <- getEnv
    ast' <- getAst
    (iModule, genv, au) <- getIr
    let
      (hasNoRealLiterals, hasNoProductOperator) = iExpBasedChecks iModule
      hasNoReferenceToReal = iClaferBasedChecks iModule
      cargs = args env
      modes = mode cargs
      stats = showStats au $ statsModule iModule
      scopes = getScopeStrategy (scope_strategy cargs) iModule

    return $ Map.fromList (
        -- result for Alloy
        (if (Alloy `elem` modes)
          then if (hasNoRealLiterals && hasNoReferenceToReal && hasNoProductOperator)
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
                         reason = "Alloy output unavailable because the model contains: "
                                ++ (if hasNoRealLiterals then "" else " | a real number literal")
                                ++ (if hasNoReferenceToReal then "" else " | a reference to a real")
                                ++ (if hasNoProductOperator then "" else " | the product operator")
                                ++ "."
                        })
                     ]
          else []
        )
        ++
        -- result for Alloy42
        (if (Alloy42 `elem` modes)
          then if (hasNoRealLiterals && hasNoReferenceToReal && hasNoProductOperator)
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
                         reason = "Alloy output unavailable because the model contains: "
                                ++ (if hasNoRealLiterals then "" else " | a real number literal")
                                ++ (if hasNoReferenceToReal then "" else " | a reference to a real")
                                ++ (if hasNoProductOperator then "" else " | the product operator")
                                ++ "."
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
                   outputCode = generateHtml env,
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
                    outputCode = genPythonModule (iModule, genv) scopes,
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
          then [ (Choco,
                  CompilerResult {
                    extension = "js",
                    outputCode = genCModule (iModule, genv) scopes,
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
  unlines [ "All clafers: " ++ (show (na + nc)) ++ " | Abstract: " ++ (show na) ++ " | Concrete: " ++ (show nc) ++ " | Reference: " ++ (show nr)
          , "Constraints: " ++ show nconst
          , "Goals: " ++ show ngoals
          , "Global scope: " ++ showInterval sgl
          , "Can skip name resolver: " ++ if au then "yes" else "no" ]

showInterval :: (Integer, Integer) -> String
showInterval (n, -1) = show n ++ "..*"
showInterval (n, m) = show n ++ ".." ++ show m

-- | The XML Schema of the IR
claferIRXSD :: String
claferIRXSD = Language.Clafer.Generator.Schema.xsd
