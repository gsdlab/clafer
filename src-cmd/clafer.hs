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
{-# LANGUAGE DeriveDataTypeable, NamedFieldPuns #-}
module Main where

import Prelude hiding (writeFile, readFile, print, putStrLn)
import qualified Data.Map as Map
import qualified Data.List as List
import Data.List.Split
import Data.Maybe
import Control.Monad.State
import System.IO
import System.Cmd
import System.Exit
import System.Timeout
import System.FilePath (dropExtension,takeBaseName)
import System.Process (readProcessWithExitCode)

import Paths_clafer
import Language.Clafer
import Language.ClaferT
import Language.Clafer.Css
import Language.Clafer.ClaferArgs
import Language.Clafer.JSONMetaData
import Language.Clafer.QNameUID
import Language.Clafer.Intermediate.Intclafer
import Language.Clafer.Generator.Html (highlightErrors)
import Language.Clafer.Generator.Graph (genSimpleGraph)

putStrV :: VerbosityL -> String -> IO ()
putStrV v s = if v > 1 then putStrLn s else return ()

run :: VerbosityL -> ClaferArgs -> InputModel -> IO ()
run _ args' input =
  do
    result <- runClaferT args' $
      do
        forM_ (fragments input) addModuleFragment
        parse
        compile
        fs <- save args'
        when (validate args') $ forM_ fs (liftIO . runValidate args' )
    if Html `elem` (mode args')
      then htmlCatch result args' input
      else return ()
    result `cth` handleErrs
  where
  cth (Left err) f = f err
  cth (Right r)  _ = return r
  fragments model = map unlines $ fragments' $ lines model
  fragments' []                  = []
  fragments' ("//# FRAGMENT":xs) = fragments' xs
  fragments' model               = takeWhile (/= "//# FRAGMENT") model : fragments' (dropWhile (/= "//# FRAGMENT") model)
--  htmlCatch :: Either ClaferErr CompilerResult -> ClaferArgs -> String -> IO(CompilerResult)
  htmlCatch (Right r) _ _ = return r
  htmlCatch (Left err) args'' model =
    do let f = (dropExtension $ file args'') ++ ".html"
       let result = (if (self_contained args'') then header ++ "<style>" ++ css ++ "</style>" ++ "</head>\n<body>\n<pre>\n" else "") ++ highlightErrors model err ++
                                                               (if (self_contained args'') then "\n</pre>\n</html>" else "")
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

save :: MonadIO m => ClaferArgs -> ClaferT m [ String ]
save args'=
  do
    resultsMap <- generate
    let results = snd $ List.unzip $ Map.toList resultsMap
    -- print stats only once
    when (not $ no_stats args') $ liftIO $ printStats results
    -- save the outputs
    (iModule, _, _) <- getIr
    forM results $ saveResult iModule resultsMap
  where
    -- saveResult :: MonadIO m => CompilerResult -> IModule -> (Map.Map ClaferMode CompilerResult) -> ClaferT m String
    saveResult iModule' resultsMap' result@CompilerResult { extension } = do
      result' <- if (add_graph args') && (Html `elem` (mode args') && ("dot" `List.isSuffixOf` (extension))) 
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

conPutStrLn :: ClaferArgs -> String -> IO ()
conPutStrLn args' s = when (not $ console_output args') $ putStrLn s

runValidate :: ClaferArgs -> String -> IO ()
runValidate args' fo = do
  let path = (tooldir args') ++ "/"
  liftIO $ putStrLn ("Validating '" ++ fo ++"'")
  let modes = mode args' 
  when (Xml `elem` modes && "xml" `List.isSuffixOf` fo) $ do
      writeFile "ClaferIR.xsd" claferIRXSD
      voidf $ system $ "java -classpath " ++ path ++ " XsdCheck ClaferIR.xsd " ++ fo
  when (Alloy `elem` modes && "als" `List.isSuffixOf` fo) $ do
    voidf $ system $ validateAlloy path "4" ++ fo
  when (Alloy42 `elem` modes && "als4" `List.isSuffixOf` fo) $ do
    voidf $ system $ validateAlloy path "4.2" ++ fo
  when (Clafer `elem` modes && "des.cfr" `List.isSuffixOf` fo) $ do  
    voidf $ system $ "../dist/build/clafer/clafer -s -m=clafer " ++ fo

validateAlloy :: String -> String -> String
validateAlloy path version = "java -cp " ++ path ++ "alloy" ++ version ++ ".jar edu.mit.csail.sdg.alloy4whole.ExampleUsingTheCompiler "

main :: IO ()
main = do
  (args', model) <- mainArgs
  let timeInSec = (timeout_analysis args') * 10^(6::Integer)
  if timeInSec > 0
    then timeout timeInSec $ start 2 args' model
    else Just `liftM` start 2 args' model
  return ()

start :: VerbosityL -> ClaferArgs -> InputModel-> IO ()
start v args' model = if schema args'
  then putStrLn claferIRXSD
  else if ecore2clafer args'
    then runEcore2Clafer (file args') $ (tooldir args')
    else run v args' model

runEcore2Clafer :: FilePath -> FilePath -> IO ()
runEcore2Clafer    ecoreFile toolPath
  | null ecoreFile = do
      putStrLn "Error: Provide a file name of an ECore model."
  | otherwise      = do
      putStrLn $ "Converting " ++ ecoreFile ++ " into Clafer"
      voidf $ system $ "java -jar " ++ toolPath ++ "/ecore2clafer.jar " ++ ecoreFile
