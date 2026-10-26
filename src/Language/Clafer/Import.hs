{-# LANGUAGE ScopedTypeVariables #-}
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

An import must be a @.cfr@ file: a URL's path must end with @.cfr@, also after a redirect, and
a URL served as HTML, JSON or XML is refused. Then a model, which may come from anyone (e.g.,
in a web tool), cannot read other files or web pages, whose text the errors would show.
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
  , isPublicAddress
  , isModelPath
  , isModelContentType
  ) where

import Control.Exception (IOException, bracketOnError, catch, displayException, fromException, try)
import Control.Monad
import Control.Monad.Except
import Control.Monad.State
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as BC
import Data.IORef
import Data.Char (isSpace, toLower)
import Data.List (dropWhileEnd, find, intercalate, isPrefixOf, isSuffixOf, nub)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Data.Text.Encoding.Error (lenientDecode)
import Data.Default (def)
import qualified Network.Connection as NC
import Network.HTTP.Client (BodyReader, HttpException (..), HttpExceptionContent (..), Manager, ManagerSettings (..), brRead, getOriginalRequest, getUri, managerSetProxy, newManager, noProxy, parseUrlThrow, responseBody, responseHeaders, responseStatus, responseTimeoutMicro, withResponse)
import qualified Network.HTTP.Client as HC (path)
import Network.HTTP.Client.Internal (Connection, makeConnection)
import Network.HTTP.Client.TLS (newTlsManager, tlsManagerSettings)
import Network.Socket (AddrInfo (..), Family (AF_INET), HostAddress, SockAddr (..), SocketType (Stream), close, connect, defaultHints, getAddrInfo, hostAddressToTuple, socket)
import Network.HTTP.Types.Header (hContentType)
import Network.HTTP.Types.Status (statusCode, statusMessage)
import Network.URI (URI (..), escapeURIString, isUnescapedInURI, parseAbsoluteURI, parseRelativeReference, relativeTo, unEscapeString, uriToString)
import System.Console.CmdArgs (cmdArgsValue)
import System.Console.CmdArgs.Explicit (process)
import System.Directory (canonicalizePath, doesFileExist)
import System.FilePath (isAbsolute, normalise, splitDirectories, takeDirectory, takeFileName, (</>))
import qualified System.IO as IO
import System.IO.Error (ioeGetErrorString)

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
  roots <- mapM canonicalizePath (import_root args')
  runExceptT $ do
    let root = file args'
        rootLocation = location root
        -- the name of the model in messages
        rootName = if null root then "<stdin>" else root
        -- the location of the model for its imports: where its text is, or --import-base
        baseLocation = if null (import_base args') then rootLocation else location (import_base args')
        fetch = readLocation (public_imports args') manager
    text <- withNewline <$> if null root then liftIO getContents else fetch False "" rootLocation
    rootOptions <- liftEither $ either (Left . inFile rootName) Right $ fileOptions text
    rootImports <- liftEither $ either (Left . inFile rootName) Right $ mapM (importLocation baseLocation) (imports rootOptions)
    rootKey <- if null root then return [] else (:[]) <$> key baseLocation
    imported <- flip execStateT ([], []) $
      forM_ (map location (imports args') ++ rootImports) $ visit fetch roots [ (k, rootName) | k <- rootKey ]
    options <- liftEither $ combineOptions (snd imported) (rootName, rootOptions)
    let localName = case rootLocation of
          Local path -> path
          Remote uri -> case takeFileName (unEscapeString (uriPath uri)) of { "" -> "model.cfr"; name -> name }
    return ( (withDefaultMode $ mergeArgs args' options){file = localName}
           , map fst (snd imported) ++ [ModelFile (if null root then rootName else showLocation rootLocation) text] )
  where
  -- the stack of the importing files (key and name), to report cycles
  visit :: (Bool -> String -> Location -> ExceptT String IO String) -> [FilePath] -> [(String, String)] -> Location -> StateT ([String], [(ModelFile, ClaferArgs)]) (ExceptT String IO) ()
  visit fetch roots stack loc = do
    let importer = maybe "the command line" snd $ safeHead stack
        name = showLocation loc
    -- before anything is known about the file, e.g., whether it exists
    unless (isModelPath $ locationPath loc) $
      throwError $ inFile importer $ "the import " ++ name ++ " is not a .cfr file"
    lift $ insideRoots importer roots loc
    k <- lift $ either (const $ return name) return =<< liftIO (runExceptT (key loc))
    when (k `elem` map fst stack) $
      throwError $ "Import cycle: " ++ intercalate " imports " (reverse (name : map snd (takeWhile ((/= k) . fst) stack) ++ [name]))
    done <- gets fst
    unless (k `elem` done) $ do
      text <- withNewline <$> lift (fetch True importer loc)
      options <- either (throwError . inFile name) return $ fileOptions text
      locations <- either (throwError . inFile name) return $ mapM (importLocation loc) (imports options)
      forM_ locations $ visit fetch roots ((k, name) : stack)
      modify $ \(done', files) -> (k : done', files ++ [(ModelFile name text, options)])
  -- identifies a file: its real path, or its URL
  key :: Location -> ExceptT String IO String
  key (Local path) = do
    exists <- liftIO $ doesFileExist path
    if exists then liftIO (canonicalizePath path) else return path
  key loc@(Remote _) = return $ showLocation loc
  safeHead xs = case xs of { x : _ -> Just x; [] -> Nothing }
  locationPath (Local path) = path
  locationPath (Remote uri) = unEscapeString $ uriPath uri
  withDefaultMode a = if null (mode a) then a{mode = [Alloy]} else a

-- | Whether a path names a Clafer model: it ends with @.cfr@.
isModelPath :: String -> Bool
isModelPath = (".cfr" `isSuffixOf`)

-- | Whether a URL's Content-Type may be a Clafer model: not HTML, JSON or XML, which web pages
--   and services are served as, whatever their URLs.
isModelContentType :: Maybe B.ByteString -> Bool
isModelContentType Nothing = True
isModelContentType (Just value) = not $
  mediaType `elem` ["text/html", "application/xhtml+xml", "application/json", "text/json", "application/xml", "text/xml"]
  || any (`isSuffixOf` mediaType) ["+json", "+xml"]
  where mediaType = map toLower $ dropWhileEnd isSpace $ dropWhile isSpace $ takeWhile (/= ';') $ BC.unpack value

-- | With import roots (--import-root), a local file must be inside one of them, after resolving
--   @..@ and symbolic links.
insideRoots :: String -> [FilePath] -> Location -> ExceptT String IO ()
insideRoots importer roots@(_ : _) (Local path) = do
  real <- liftIO $ canonicalizePath path
  unless (any (\r -> splitDirectories r `isPrefixOf` splitDirectories real) roots) $
    throwError $ inFile importer $ "the import " ++ path ++ " is outside the folders from which files can be imported"
insideRoots _ _ _ = return ()

-- | The largest file that is downloaded.
maxDownload :: Int
maxDownload = 16 * 1024 * 1024

-- | Reads a file or downloads a URL, from a public address only if @public@; the importer names
--   the file importing it, for messages. An import, downloaded after redirects, must still be a
--   @.cfr@ file and not be served as a web page ('isModelContentType').
readLocation :: Bool -> IORef (Maybe Manager) -> Bool -> String -> Location -> ExceptT String IO String
readLocation _ _ _ importer (Local path) = do
  exists <- liftIO $ doesFileExist path
  unless exists $ throwError $ inFile importer $ "the file " ++ path ++ " does not exist"
  liftIO $ IO.withFile path IO.ReadMode $ \h -> do
    s <- IO.hGetContents h
    length s `seq` return s
readLocation public managerRef isImport importer loc@(Remote uri) = do
  manager <- liftIO $ readIORef managerRef >>= maybe (newManager' >>= \m -> writeIORef managerRef (Just m) >> return m) return
  result <- liftIO $ try $ do
    request <- parseUrlThrow $ showLocation loc
    withResponse request manager $ \response -> do
      -- the request of the response, after redirects
      let final = getOriginalRequest response
          contentType = lookup hContentType $ responseHeaders response
      if isImport && not (isModelPath $ unEscapeString $ BC.unpack $ HC.path final)
      then return $ Left $ "redirected to " ++ uriToString id (getUri final) "" ++ ", which is not a .cfr file"
      else if isImport && not (isModelContentType contentType)
      then return $ Left $ "it is served as " ++ maybe "" BC.unpack contentType ++ ", not as a Clafer model"
      else maybe (Left $ "larger than " ++ show (maxDownload `div` (1024 * 1024)) ++ " MB") Right
             <$> readBody 0 [] (responseBody response)
  case result of
    Right (Left problem) -> throwError $ inFile importer $ "cannot read " ++ showLocation loc ++ ": " ++ problem
    Right (Right body) -> return $ T.unpack $ TE.decodeUtf8With lenientDecode body
    Left (HttpExceptionRequest _ (StatusCodeException response _)) ->
      throwError $ inFile importer $ "cannot read " ++ showLocation loc ++ ": HTTP "
        ++ show (statusCode $ responseStatus response) ++ " " ++ T.unpack (TE.decodeUtf8With lenientDecode $ statusMessage $ responseStatus response)
    Left (HttpExceptionRequest _ (ConnectionFailure e)) -> throwError $ inFile importer $ "cannot read " ++ showLocation loc ++ ": "
      ++ maybe (displayException e) ioeGetErrorString (fromException e)
    Left (HttpExceptionRequest _ content) -> throwError $ inFile importer $ "cannot read " ++ showLocation loc ++ ": " ++ show content
    Left (InvalidUrlException _ reason) -> throwError $ inFile importer $ "invalid URL " ++ uriToString id uri "" ++ ": " ++ reason
  where
  newManager' = if public then newManager publicManagerSettings else newTlsManager
  -- the body, unless it is larger than maxDownload
  readBody :: Int -> [B.ByteString] -> BodyReader -> IO (Maybe B.ByteString)
  readBody size chunks reader = do
    chunk <- brRead reader
    let size' = size + B.length chunk
    if B.null chunk then return $ Just $ B.concat $ reverse chunks
    else if size' > maxDownload then return Nothing
    else readBody size' (chunk : chunks) reader

-- | Connections to public addresses only: the address is checked when connecting (also after a
--   redirect), and the connection is made to that address; no proxy.
publicManagerSettings :: ManagerSettings
publicManagerSettings = managerSetProxy noProxy tlsManagerSettings
  { managerRawConnection = do
      raw <- managerRawConnection tlsManagerSettings
      return $ \_ host port -> do
        address <- publicAddress host
        raw (Just address) host port
  , managerTlsConnection = do
      context <- NC.initConnectionContext
      return $ \_ host port -> do
        address <- publicAddress host
        tlsConnection context address host port
  , managerResponseTimeout = responseTimeoutMicro 30000000
  }

-- | A public IPv4 address of the host, or an error.
publicAddress :: String -> IO HostAddress
publicAddress host = do
  infos <- getAddrInfo (Just defaultHints{ addrFamily = AF_INET, addrSocketType = Stream }) (Just host) Nothing
  case find isPublicAddress [ a | SockAddrInet _ a <- map addrAddress infos ] of
    Just address -> return address
    Nothing -> ioError $ userError $ "the host " ++ host ++ " has no public address"

-- | A TLS connection to the address, for the host.
tlsConnection :: NC.ConnectionContext -> HostAddress -> String -> Int -> IO Connection
tlsConnection context address host port =
  bracketOnError (socket AF_INET Stream 0) close $ \sock -> do
    connect sock (SockAddrInet (fromIntegral port) address)
    conn <- NC.connectFromSocket context sock NC.ConnectionParams
      { NC.connectionHostname = host
      , NC.connectionPort = fromIntegral port
      , NC.connectionUseSecure = Just def  -- validates the certificate for the host
      , NC.connectionUseSocks = Nothing
      }
    makeConnection (NC.connectionGetChunk conn) (NC.connectionPut conn)
      (NC.connectionClose conn `catch` \(_ :: IOException) -> return ())

-- | Whether an IPv4 address is public: not unspecified, loopback, private, shared, link-local,
--   reserved, benchmarking, multicast or broadcast.
isPublicAddress :: HostAddress -> Bool
isPublicAddress address = not $ case hostAddressToTuple address of
  (0, _, _, _)                       -> True
  (10, _, _, _)                      -> True
  (100, b, _, _) | b >= 64 && b < 128 -> True
  (127, _, _, _)                     -> True
  (169, 254, _, _)                   -> True
  (172, b, _, _) | b >= 16 && b < 32  -> True
  (192, 0, 0, _)                     -> True
  (192, 0, 2, _)                     -> True
  (192, 168, _, _)                   -> True
  (198, b, _, _) | b == 18 || b == 19 -> True
  (198, 51, 100, _)                  -> True
  (203, 0, 113, _)                   -> True
  (a, _, _, _)                       -> a >= 224

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
* the options of the compilation rather than of the model (e.g., @-s@, @-o@) are only allowed
  in the model, not in an imported file;
* the options that run tools or restrict the imports (@-v@, @--tooldir@, @--import-root@,
  @--public-imports@, @--import-base@) are only allowed on the command line: a model, which may
  come from anyone, cannot set them for itself.
-}
combineOptions :: [(ModelFile, ClaferArgs)] -> (FilePath, ClaferArgs) -> Either String ClaferArgs
combineOptions imported (root, rootOptions) = do
  forM_ ((root, rootOptions) : files) $ \(path, options) ->
    case [ name' | (name', isChanged) <- commandLineOptions, isChanged options ] of
      []     -> return ()
      names' -> Left $ inFile path $ theOptions names' ++ " can only be given on the command line, not in //# OPTIONS"
  forM_ imported $ \(ModelFile path _, options) ->
    case [ name' | (name', isChanged) <- runOptions, isChanged options ] of
      []     -> return ()
      names' -> Left $ inFile path $ theOptions names'
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
    [ ("-o", changed console_output), ("-s", changed no_stats)
    , ("-a", changed alloy_mapping), ("--self-contained", changed self_contained)
    , ("--add-graph", changed add_graph), ("--sr", changed show_references), ("--add-comments", changed add_comments)
    , ("--meta-data", changed meta_data), ("--ecore2clafer", changed ecore2clafer), ("a model file", changed file) ]
  theOptions [name'] = "the option " ++ name'
  theOptions names' = "the options " ++ intercalate ", " names'
  -- the options that run tools or restrict the imports, which a model cannot set for itself
  commandLineOptions =
    [ ("-v", changed validate), ("--tooldir", changed tooldir), ("--import-root", changed import_root)
    , ("--public-imports", changed public_imports), ("--import-base", changed import_base) ]
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
