{-
 Copyright (C) 2012-2013 Kacper Bak, Jimmy Liang <http://gsd.uwaterloo.ca>

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
{-# LANGUAGE DeriveDataTypeable #-}
module Main where

import Prelude hiding (writeFile, readFile, print, putStrLn)

import System.IO
import System.Cmd
import System.Exit
import System.Timeout
import Control.Monad.State
import System.FilePath (dropExtension,takeBaseName)
import System.Process (readProcessWithExitCode)

import Language.Clafer
import Language.ClaferT
import Language.Clafer.Css
import Language.Clafer.ClaferArgs
import Language.Clafer.Generator.Html (highlightErrors)
import Language.Clafer.Generator.Graph (genSimpleGraph)

putStrV :: VerbosityL -> String -> IO ()
putStrV v s = if v > 1 then putStrLn s else return ()

run :: VerbosityL -> ClaferArgs -> InputModel -> IO ()
run _ args' input =
  do
    result <- runClaferT args' $
      do
        addFragments $ fragments input
        parse
        compile
        f' <- save
        when (validate args') $ liftIO $ runValidate args' f'
    if mode args' == Html
      then htmlCatch result args' input
      else return ()
    result `cth` handleErrs
  where
  cth (Left err) f = f err
  cth (Right r)  _ = return r
  addFragments []     = return ()
  addFragments (x:xs) = addModuleFragment x >> addFragments xs
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
  handleErr _ = error "Function handleErr from Main file was given an invalid argument"

  save =
    do
      result <- generate
      (iModule, _, _) <- getIr
      result' <- if (add_graph args') && (mode args' == Html) 
             then do
                   ast' <- getAst
                   (_, graph, _) <- liftIO $ readProcessWithExitCode "dot"  ["-Tsvg"] $ genSimpleGraph ast' iModule (takeBaseName $ file args') (show_references args')
                   return $ summary graph result
                 else return result
      liftIO $ when (not $ no_stats args') $ putStrLn (statistics result')
      let f = dropExtension $ file args'
      let f' = f ++ "." ++ (extension result)
      liftIO $ if console_output args' then putStrLn (outputCode result') else writeFile f' (outputCode result')
      liftIO $ when (alloy_mapping args') $ writeFile (f ++ "." ++ "map") $ show (mappingToAlloy result')
      return f'
  summary graph result = result{outputCode=unlines $ summary' graph ("<pre>" ++ statistics result ++ "</pre>") (lines $ outputCode result)}
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
  liftIO $ putStrLn ("tooldir=" ++ path)
  case (mode args') of
    Xml -> do
      writeFile "ClaferIR.xsd" claferIRXSD
      voidf $ system $ "java -classpath " ++ path ++ " XsdCheck ClaferIR.xsd " ++ fo
    Alloy ->   voidf $ system $ validateAlloy path "4" ++ fo
    Alloy42 -> voidf $ system $ validateAlloy path "4.2" ++ fo
    Clafer ->  voidf $ system $ path ++ "/clafer -s -m=clafer " ++ fo
    _ -> error "Function runValidate from Main file was given an invalid mode"

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
      putStrLn "Error: Provide a file name of the ECore model."
  | otherwise      = do
      putStrLn $ "Converting " ++ ecoreFile ++ " into Clafer"
      voidf $ system $ "java -jar " ++ toolPath ++ "ecore2clafer.jar " ++ ecoreFile

