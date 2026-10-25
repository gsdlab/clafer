{-
 Copyright (C) 2026 Michal Antkiewicz <http://gsd.uwaterloo.ca>

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
{- | Models made of several files: a model imports other files with the option
@--import=FILE@, in its @//# OPTIONS@ directive or on the command line. The imported
files are compiled with the model as one model, with one namespace, before it and
each only once; their options are combined with the model's ('combineOptions').

A model and its imports are local files or URLs (@http://@, @https://@). An import is
relative to the importing file: to its folder, or to its URL. A model read from a URL
may only import URLs.
-}
module Language.Clafer.Import
  ( ModelFile (..)
  , Location (..)
  , readModel
  , location
  , importLocation
  , fileOptions
  , combineOptions
  , modelText
  , modelPosition
  , fileStarts
  ) where

import Control.Exception (try)
import Control.Monad
import Control.Monad.Except
import Control.Monad.State
import qualified Data.ByteString.Lazy as BL
import Data.IORef
import Data.List (intercalate, isPrefixOf, nub)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Data.Text.Encoding.Error (lenientDecode)
import Network.HTTP.Client (HttpException (..), HttpExceptionContent (..), Manager, httpLbs, parseUrlThrow, responseBody, responseStatus)
import Network.HTTP.Client.TLS (newTlsManager)
import Network.HTTP.Types.Status (statusCode, statusMessage)
import Network.URI (URI (..), escapeURIString, isUnescapedInURI, parseAbsoluteURI, parseRelativeReference, relativeTo, unEscapeString, uriToString)
import System.Console.CmdArgs (cmdArgsValue)
import System.Console.CmdArgs.Explicit (process)
import System.Directory (canonicalizePath, doesFileExist)
import System.FilePath (isAbsolute, normalise, takeDirectory, takeFileName, (</>))
import qualified System.IO as IO

import Language.Clafer.ClaferArgs
import Language.Clafer.SplitJoin (splitArgs)

-- | A file of a model and its text, which ends with a newline.
data ModelFile = ModelFile
  { modelFilePath :: FilePath  -- ^ its path or URL, as shown in messages
  , modelFileText :: String
  } deriving (Eq, Show)

-- | Where a file of a model is: a local path, or a URL (http or https).
data Location = Local FilePath | Remote URI
  deriving (Eq, Show)

-- | The location of a model file name: a URL with @http://@ or @https://@, otherwise a local
--   path (a @file://@ URL is its path).
location :: String -> Location
location name = case parseAbsoluteURI name of
  Just uri | uriScheme uri `elem` ["http:", "https:"] -> Remote uri
  _ | "file://" `isPrefixOf` name -> Local $ unEscapeString $ drop 7 name
    | otherwise                   -> Local name

-- | The location of an import, relative to the importing file: to its folder, or to its URL.
--   A file read from a URL may only import URLs.
importLocation :: Location -> String -> Either String Location
importLocation importer name = case (location name, importer) of
  (Remote uri, _) -> Right $ Remote uri
  (Local path, Local importerPath) -> Right $ Local $ normalise $ takeDirectory importerPath </> path
  (Local path, Remote base)
    | "file://" `isPrefixOf` name || isAbsolute path -> Left $ "a model read from a URL cannot import the local file " ++ name
    | otherwise -> case parseRelativeReference (escapeURIString isUnescapedInURI path) of
        Just reference -> Right $ Remote $ reference `relativeTo` base
        Nothing        -> Left $ "the import " ++ name ++ " is not a valid relative URL"

-- | How a location is shown in messages.
showLocation :: Location -> String
showLocation (Local path) = path
showLocation (Remote uri) = uriToString id uri ""

-- | Reads the model given by the arguments (the file or URL 'file', or the standard input if it
--   is empty) and the files it imports, transitively. Returns the arguments combined with the
--   options of all files (the given arguments take precedence) and the files: imported files
--   before the files importing them, each once, and the model last. For a model read from a
--   URL, 'file' becomes the last segment of the URL's path, which names the outputs.
readModel :: ClaferArgs -> IO (Either String (ClaferArgs, [ModelFile]))
readModel args' = do
  manager <- newIORef Nothing  -- created at the first URL
  runExceptT $ do
    let root = file args'
        rootLocation = location root
        -- the name of the model in messages
        rootName = if null root then "<stdin>" else root
    text <- withNewline <$> if null root then liftIO getContents else readLocation manager "" rootLocation
    rootOptions <- liftEither $ either (Left . inFile rootName) Right $ fileOptions text
    rootImports <- liftEither $ either (Left . inFile rootName) Right $ mapM (importLocation rootLocation) (imports rootOptions)
    rootKey <- if null root then return [] else (:[]) <$> key rootLocation
    imported <- flip execStateT ([], []) $
      forM_ (map location (imports args') ++ rootImports) $ visit manager [ (k, rootName) | k <- rootKey ]
    options <- liftEither $ combineOptions (snd imported) (rootName, rootOptions)
    let localName = case rootLocation of
          Local path -> path
          Remote uri -> case takeFileName (unEscapeString (uriPath uri)) of { "" -> "model.cfr"; name -> name }
    return ( (withDefaultMode $ mergeArgs args' options){file = localName}
           , map fst (snd imported) ++ [ModelFile (if null root then rootName else showLocation rootLocation) text] )
  where
  -- the stack of the importing files (key and name), to report cycles
  visit :: IORef (Maybe Manager) -> [(String, String)] -> Location -> StateT ([String], [(ModelFile, ClaferArgs)]) (ExceptT String IO) ()
  visit manager stack loc = do
    let importer = maybe "the command line" snd $ safeHead stack
        name = showLocation loc
    k <- lift $ either (const $ return name) return =<< liftIO (runExceptT (key loc))
    when (k `elem` map fst stack) $
      throwError $ "Import cycle: " ++ intercalate " imports " (reverse (name : map snd (takeWhile ((/= k) . fst) stack) ++ [name]))
    done <- gets fst
    unless (k `elem` done) $ do
      text <- withNewline <$> lift (readLocation manager importer loc)
      options <- either (throwError . inFile name) return $ fileOptions text
      locations <- either (throwError . inFile name) return $ mapM (importLocation loc) (imports options)
      forM_ locations $ visit manager ((k, name) : stack)
      modify $ \(done', files) -> (k : done', files ++ [(ModelFile name text, options)])
  -- identifies a file: its real path, or its URL
  key :: Location -> ExceptT String IO String
  key (Local path) = do
    exists <- liftIO $ doesFileExist path
    if exists then liftIO (canonicalizePath path) else return path
  key loc@(Remote _) = return $ showLocation loc
  safeHead xs = case xs of { x : _ -> Just x; [] -> Nothing }
  withDefaultMode a = if null (mode a) then a{mode = [Alloy]} else a

-- | Reads a file or downloads a URL; the importer names the file importing it, for messages.
readLocation :: IORef (Maybe Manager) -> String -> Location -> ExceptT String IO String
readLocation _ importer (Local path) = do
  exists <- liftIO $ doesFileExist path
  unless exists $ throwError $ inFile importer $ "the file " ++ path ++ " does not exist"
  liftIO $ IO.withFile path IO.ReadMode $ \h -> do
    s <- IO.hGetContents h
    length s `seq` return s
readLocation managerRef importer loc@(Remote uri) = do
  manager <- liftIO $ readIORef managerRef >>= maybe (newTlsManager >>= \m -> writeIORef managerRef (Just m) >> return m) return
  result <- liftIO $ try $ do
    request <- parseUrlThrow $ showLocation loc
    httpLbs request manager
  case result of
    Right response -> return $ T.unpack $ TE.decodeUtf8With lenientDecode $ BL.toStrict $ responseBody response
    Left (HttpExceptionRequest _ (StatusCodeException response _)) ->
      throwError $ inFile importer $ "cannot read " ++ showLocation loc ++ ": HTTP "
        ++ show (statusCode $ responseStatus response) ++ " " ++ T.unpack (TE.decodeUtf8With lenientDecode $ statusMessage $ responseStatus response)
    Left (HttpExceptionRequest _ content) -> throwError $ inFile importer $ "cannot read " ++ showLocation loc ++ ": " ++ show content
    Left (InvalidUrlException _ reason) -> throwError $ inFile importer $ "invalid URL " ++ uriToString id uri "" ++ ": " ++ reason

inFile :: FilePath -> String -> String
inFile path message = (if null path then "" else path ++ ": ") ++ message

withNewline :: String -> String
withNewline s = if null s || last s == '\n' then s else s ++ "\n"

-- | The options of a model's @//# OPTIONS@ directive, its first line; the defaults without one.
fileOptions :: String -> Either String ClaferArgs
fileOptions model
  | "//# OPTIONS " `isPrefixOf` model =
      either (Left . ("//# OPTIONS: " ++)) (Right . cmdArgsValue) $
        process claferMode $ splitArgs $ filter (/= '\r') $ drop 12 $ takeWhile (/= '\n') model
  | otherwise = Right claferDefaults

{- | Combines the options of the imported files and of the model:

* the largest @--maxint@, @--tl@ and @--timeout-analysis@, the smallest @--minint@;
* all modes (@-m@) and imports;
* @-k@, @-c@, @--check-afm@ and @-i@ if any file has them, @-f@ only if all files have it;
* the layout (@-l@, @--nl@) and the scope strategy (@--ss@) must be the same in all files,
  since the files are parsed together;
* the options of the compilation rather than of the model (e.g., @-v@, @--tooldir@, @-s@)
  are only allowed in the model, not in an imported file.
-}
combineOptions :: [(ModelFile, ClaferArgs)] -> (FilePath, ClaferArgs) -> Either String ClaferArgs
combineOptions imported (root, rootOptions) = do
  forM_ imported $ \(ModelFile path _, options) ->
    case [ name' | (name', isChanged) <- runOptions, isChanged options ] of
      []     -> return ()
      names' -> Left $ inFile path $ "the options " ++ intercalate ", " names'
                  ++ " can only be given in the compiled model or on the command line, not in an imported file"
  forM_ sameOptions $ \(name', isDifferent) ->
    case [ path | (path, options) <- files, isDifferent options rootOptions ] of
      []    -> return ()
      paths -> Left $ "The option " ++ name' ++ " must be the same in all files of the model: it differs in "
                 ++ intercalate ", " paths ++ " from " ++ root
  return rootOptions
    { mode                = nub $ concatMap mode all'
    , imports             = nub $ concatMap imports all'
    , maxint              = maximumOf $ map maxint all'
    , minint              = minimumOf $ map minint all'
    , trace_len           = maximum $ map trace_len all'
    , timeout_analysis    = maximum $ map timeout_analysis all'
    , keep_unused         = any keep_unused all'
    , check_duplicates    = any check_duplicates all'
    , afm                 = any afm all'
    , flatten_inheritance = any flatten_inheritance all'
    , skip_resolver       = all skip_resolver all'
    }
  where
  files = [ (path, options) | (ModelFile path _, options) <- imported ]
  all' = rootOptions : map snd files
  maximumOf xs = case [ x | Just x <- xs ] of { [] -> Nothing; ys -> Just (maximum ys) }
  minimumOf xs = case [ x | Just x <- xs ] of { [] -> Nothing; ys -> Just (minimum ys) }
  -- the options of the compilation, which differ from the defaults
  runOptions =
    [ ("-o", changed console_output), ("-s", changed no_stats), ("-v", changed validate)
    , ("--tooldir", changed tooldir), ("-a", changed alloy_mapping), ("--self-contained", changed self_contained)
    , ("--add-graph", changed add_graph), ("--sr", changed show_references), ("--add-comments", changed add_comments)
    , ("--meta-data", changed meta_data), ("--ecore2clafer", changed ecore2clafer), ("a model file", changed file) ]
  changed :: Eq a => (ClaferArgs -> a) -> ClaferArgs -> Bool
  changed f options = f options /= f claferDefaults
  sameOptions =
    [ ("-l", differs no_layout), ("--nl", differs new_layout), ("--ss", differs scope_strategy) ]
  differs :: Eq a => (ClaferArgs -> a) -> ClaferArgs -> ClaferArgs -> Bool
  differs f a b = f a /= f b

-- | The text of the complete model: the files in order.
modelText :: [ModelFile] -> String
modelText = concatMap modelFileText

-- | The files and the lines of the complete model where they start (lines from 1).
fileStarts :: [ModelFile] -> [(Integer, FilePath)]
fileStarts files = zip (scanl (+) 1 [ fromIntegral $ length $ filter (== '\n') text | ModelFile _ text <- files ]) (map modelFilePath files)

-- | The file and the line in it of a line of the complete model (lines from 1).
modelPosition :: [ModelFile] -> Integer -> (FilePath, Integer)
modelPosition files line = go 1 files
  where
  go _ [] = ("", line)
  go start (ModelFile path text : rest)
    | null rest || line < start + size = (path, line - start + 1)
    | otherwise                        = go (start + size) rest
    where size = fromIntegral $ length $ filter (== '\n') text
