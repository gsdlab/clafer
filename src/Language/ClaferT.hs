{-# LANGUAGE RankNTypes #-}
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

{- |
This is in a separate module from the module "Language.Clafer" so that other modules that require
ClaferEnv can just import this module without all the parsing/compiline/generating functionality.
 -}
module Language.ClaferT
  ( ClaferEnv(..)
  , irModuleTrace
  , uidIClaferMap
  , makeEnv
  , getAst
  , getIr
  , ClaferM
  , ClaferT
  , CErr(..)
  , CErrs(..)
  , ClaferErr
  , ClaferErrs
  , ClaferSErr
  , ClaferSErrs
  , ErrPos(..)
  , PartialErrPos(..)
  , throwErrs
  , throwErr
  , catchErrs
  , getEnv
  , getsEnv
  , modifyEnv
  , putEnv
  , runClafer
  , runClaferT
  , Throwable(..)
  , Span(..)
  , Pos(..)
  ) where

import           Control.Monad.Except
import           Control.Monad.Identity
import           Control.Monad.State
import           Data.List
import qualified Data.Map as Map

import           Language.Clafer.ClaferArgs
import           Language.Clafer.Common
import           Language.Clafer.Front.AbsClafer
import           Language.Clafer.Intermediate.Intclafer
import           Language.Clafer.Intermediate.Tracing

{-
 - Examples.
 -
 - If you need ClaferEnv:
 -   runClafer args $
 -     do
 -       env <- getEnv
 -       env' = ...
 -       putEnv env'
 -
 - Remember to putEnv if you do any modification to the ClaferEnv or else your updates
 - are lost!
 -
 -
 - Throwing errors:
 -
 -   throwErr $ ParseErr (ErrFragPos fragId fragPos) "failed parsing"
 -   throwErr $ ParseErr (ErrModelPos modelPos) "failed parsing"
 -
 - There is two ways of defining the position of the error. Either define the position
 - relative to a fragment, or relative to the model. Pick the one that is convenient.
 - Once thrown, the "partial" positions will be automatically updated to contain both
 - the model and fragment positions.
 - Use throwErrs to throw multiple errors.
 - Use catchErrs to catch errors (usually not needed).
 -
 -}

data ClaferEnv
  = ClaferEnv
    { args           :: ClaferArgs
    , modelFrags     :: [String] -- original text of the model fragments
    , cAst           :: Maybe Module
    , cIr            :: Maybe (IModule, GEnv, Bool)
    , frags          :: [Pos]    -- line numbers of fragment markers
    , astModuleTrace :: Map.Map Span [Ast]  -- can keep the Ast map since it never changes
    } deriving Show

-- | This simulates a field in the ClaferEnv that will always recompute the map,
--   since the IR always changes and the map becomes obsolete
irModuleTrace :: ClaferEnv -> Map.Map Span [Ir]
irModuleTrace env = traceIrModule $ getIModule $ cIr env
  where
    getIModule (Just (imodule, _, _)) = imodule
    getIModule Nothing                = error "BUG: irModuleTrace: cannot request IR map before desugaring."

-- | This simulates a field in the ClaferEnv that will always recompute the map,
--   since the IR always changes and the map becomes obsolete
--   maps from a UID to an IClafer with the given UID
uidIClaferMap :: ClaferEnv -> UIDIClaferMap
uidIClaferMap env = createUidIClaferMap $ getIModule $ cIr env
  where
    getIModule (Just (iModule, _, _)) = iModule
    getIModule Nothing                = error "BUG: uidIClaferMap: cannot request IClafer map before desugaring."

getAst :: (Monad m) => ClaferT m Module
getAst = do
  env <- getEnv
  case cAst env of
    (Just a) -> return a
    _ -> throwErr (ClaferErr "No AST. Did you forget to add fragments or parse?" :: CErr Span) -- Indicates a bug in the Clafer translator.

getIr :: (Monad m) => ClaferT m (IModule, GEnv, Bool)
getIr = do
  env <- getEnv
  case cIr env of
    (Just i) -> return i
    _ -> throwErr (ClaferErr "No IR. Did you forget to compile?" :: CErr Span) -- Indicates a bug in the Clafer translator.

makeEnv :: ClaferArgs -> ClaferEnv
makeEnv args' =
  ClaferEnv
    { args = args''
    , modelFrags = []
    , cAst = Nothing
    , cIr = Nothing
    , frags = []
    , astModuleTrace = Map.empty
    }
  where
    args'' = if (CVLGraph `elem` (mode args') ||
                 Html `elem` (mode args') ||
                 Graph `elem` (mode args'))
              then args'{keep_unused=True}
              else args'

-- | Monad for using Clafer.
type ClaferM = ClaferT Identity

-- | Monad Transformer for using Clafer.
type ClaferT m = ExceptT ClaferErrs (StateT ClaferEnv m)

type ClaferErr = CErr ErrPos
type ClaferErrs = CErrs ErrPos

type ClaferSErr = CErr Span
type ClaferSErrs = CErrs Span

-- | Possible errors that can occur when using Clafer
-- | Generate errors using throwErr/throwErrs:
data CErr p
  -- | Generic error
  = ClaferErr
    { msg :: String
    }
  -- | Error generated by the parser
  | ParseErr
    { pos :: p -- ^ Position of the error
    , msg :: String
    }
  -- | Error generated by semantic analysis
  | SemanticErr
    { pos :: p
    , msg :: String
    }
  deriving Show

-- | Clafer keeps track of multiple errors.
data CErrs p =
  ClaferErrs {errs :: [CErr p]}
  deriving Show

data ErrPos =
  ErrPos {
    -- | The fragment where the error occurred.
    fragId   :: Int,
    -- | Error positions are relative to their fragments.
    -- | For example an error at (Pos 2 3) means line 2 column 3 of the fragment, not the entire model.
    fragPos  :: Pos,
    -- | The error position relative to the model.
    modelPos :: Pos
  }
  deriving Show


-- | The full ErrPos requires lots of information that needs to be consistent. Every time we throw an error,
-- | we need BOTH the (fragId, fragPos) AND modelPos. This makes it easier for developers using ClaferT so they
-- | only need to provide part of the information and the rest is automatically calculated. The code using
-- | ClaferT is more concise and less error-prone.
-- |
-- |   modelPos <- modelPosFromFragPos fragdId fragPos
-- |   throwErr $ ParserErr (ErrPos fragId fragPos modelPos)
-- |
-- |     vs
-- |
-- |   throwErr $ ParseErr (ErrFragPos fragId fragPos)
-- |
-- | Hopefully making the error handling easier will make it more universal.
data PartialErrPos =
  -- | Position relative to the start of the fragment. Will calculate model position automatically.
  -- | fragId starts at 0
  -- | The position is relative to the start of the fragment.
  ErrFragPos {
    pFragId  :: Int,
    pFragPos :: Pos
  } |
  ErrFragSpan {
    pFragId   :: Int,
    pFragSpan :: Span
  } |
  -- | Position relative to the start of the complete model. Will calculate fragId and fragPos automatically.
  -- | The position is relative to the entire complete model.
  ErrModelPos {
    pModelPos :: Pos
  }
  |
  ErrModelSpan {
    pModelSpan :: Span
  }
  deriving Show

class ClaferErrPos p where
  toErrPos :: Monad m => p -> ClaferT m ErrPos

instance ClaferErrPos Span where
  toErrPos = toErrPos . ErrModelSpan

instance ClaferErrPos ErrPos where
  toErrPos = return . id

instance ClaferErrPos PartialErrPos where
  toErrPos (ErrFragPos frgId frgPos) =
    do
      f <- getsEnv frags
      let pos' = ((Pos 1 1 : f) !! frgId) `addPos` frgPos
      return $ ErrPos frgId frgPos pos'
  toErrPos (ErrFragSpan frgId (Span frgPos _)) = toErrPos $ ErrFragPos frgId frgPos
  toErrPos (ErrModelPos modelPos') =
    do
      f <- getsEnv frags
      let fragSpans = zipWith Span (Pos 1 1 : f) f
      case findFrag modelPos' fragSpans of
        Just (frgId, Span fragStart _) -> return $ ErrPos frgId (modelPos' `minusPos` fragStart) modelPos'
        Nothing -> return $ ErrPos 1 noPos noPos -- error $ show modelPos' ++ " not within any frag spans: " ++ show fragSpans -- Indicates a bug in the Clafer translator
    where
    findFrag pos'' spans =
      find (inSpan pos'' . snd) (zip [0..] spans)
  toErrPos (ErrModelSpan (Span modelPos'' _)) = toErrPos $ ErrModelPos modelPos''

class Throwable t where
  toErr :: t -> Monad m => ClaferT m ClaferErr

instance ClaferErrPos p => Throwable (CErr p) where
  toErr (ClaferErr mesg) = return $ ClaferErr mesg
  toErr err =
    do
      pos' <- toErrPos $ pos err
      return $ err{pos = pos'}

-- | Throw many errors.
throwErrs :: (Monad m, Throwable t) => [t] -> ClaferT m a
throwErrs throws =
  do
    errors <- mapM toErr throws
    throwError $ ClaferErrs errors

-- | Throw one error.
throwErr :: (Monad m, Throwable t) => t -> ClaferT m a
throwErr throw = throwErrs [throw]

-- | Catch errors
catchErrs :: Monad m => ClaferT m a -> ([ClaferErr] -> ClaferT m a) -> ClaferT m a
catchErrs e h = e `catchError` (h . errs)

addPos :: Pos -> Pos -> Pos
addPos (Pos l c) (Pos 1 d) = Pos l (c + d - 1)    -- Same line
addPos (Pos l _) (Pos m d) = Pos (l + m - 1) d    -- Different line
minusPos :: Pos -> Pos -> Pos
minusPos (Pos l c) (Pos 1 d) = Pos l (c - d + 1)  -- Same line
minusPos (Pos l c) (Pos m _) = Pos (l - m + 1) c  -- Different line

inSpan :: Pos -> Span -> Bool
inSpan pos' (Span start end) = pos' >= start && pos' <= end

-- | Get the ClaferEnv
getEnv :: Monad m => ClaferT m ClaferEnv
getEnv = get

getsEnv :: Monad m => (ClaferEnv -> a) -> ClaferT m a
getsEnv = gets

-- | Modify the ClaferEnv
modifyEnv :: Monad m => (ClaferEnv -> ClaferEnv) -> ClaferT m ()
modifyEnv = modify

-- | Set the ClaferEnv. Remember to set the env after every change.
putEnv :: Monad m => ClaferEnv -> ClaferT m ()
putEnv = put

-- | Uses the ErrorT convention:
-- |   Left is for error (a string containing the error message)
-- |   Right is for success (with the result)
runClaferT :: Monad m => ClaferArgs -> ClaferT m a -> m (Either [ClaferErr] a)
runClaferT args' exec =
  mapLeft errs `liftM` evalStateT (runExceptT exec) (makeEnv args')
  where
  mapLeft :: (a -> c) -> Either a b -> Either c b
  mapLeft f (Left l) = Left (f l)
  mapLeft _ (Right r) = Right r

-- | Convenience
runClafer :: ClaferArgs -> ClaferM a -> Either [ClaferErr] a
runClafer args' = runIdentity . runClaferT args'
