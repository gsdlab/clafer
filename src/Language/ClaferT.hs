{-# LANGUAGE RankNTypes, FlexibleContexts #-}
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

{-
 - This is in a separate module from Language.Clafer so that other modules that require
 - ClaferEnv can just import this module without all the parsing/compiline/generating
 - functionality.
 -}
module Language.ClaferT (
                         ClaferEnv(..), 
                         makeEnv, 
                         getAst, 
                         getIr, 
                         ClaferM, 
                         ClaferT, 
                         CErr(..), 
                         CErrs(..), 
                         ClaferErr, 
                         ClaferErrs, 
                         ClaferSErr, 
                         ClaferSErrs, 
                         ErrPos(..), 
                         PartialErrPos(..), 
                         throwErrs, 
                         throwErr, 
                         catchErrs, 
                         getEnv, 
                         getsEnv, 
                         modifyEnv, 
                         putEnv, 
                         runClafer, 
                         runClaferT, 
                         Throwable(..), 
                         Span(..), 
                         Pos(..),
                         SnapShots,
                         takeSnapShot, 
                         SnapShotId(..), 
                         numberOfSS, 
                         runClaferS
) where

import Control.Monad.Error
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.Identity
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map

import Language.Clafer.Common
import Language.Clafer.Front.Absclafer
import Language.Clafer.Intermediate.Tracing
import Language.Clafer.Intermediate.Intclafer
import Language.Clafer.ClaferArgs

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

data ClaferEnv = ClaferEnv {
                            args :: ClaferArgs,
                            modelFrags :: [String], -- original text of the model fragments
                            cAst :: Maybe Module,
                            cIr :: Maybe (IModule, GEnv, Bool),
                            frags :: [Pos],    -- line numbers of fragment markers
                            irModuleTrace :: Map Span [Ir],
                            astModuleTrace :: Map Span [Ast]
                            } deriving (Show, Eq)

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
makeEnv args' = ClaferEnv { args = args'',
                           modelFrags = [],
                           cAst = Nothing,
                           cIr = Nothing,
                           frags = [],
                           irModuleTrace = Map.empty,
                           astModuleTrace = Map.empty}
               where args'' = case mode args' of
                               CVLGraph -> args'{flatten_inheritance=True, keep_unused=True}
                               Html     -> args'{keep_unused=True}
                               Graph    -> args'{keep_unused=True}
                               _             -> args'


data SnapShotId = Start | Parsed | Mapped | Desugared | FoundDuplicates | NameResolved 
                  | InheritanceResolved | TypeResolved | Transformed | Optimized 
                  | Compiled deriving (Show, Ord, Eq)
numberOfSS :: Int
numberOfSS = 11 -- REMEMBER TO UPDATE THIS WHEN ADDING SNAPSHOTS!

type SnapShots = (Map.Map SnapShotId ClaferEnv) 

takeSnapShot :: MonadWriter (Map SnapShotId ClaferEnv) m => ClaferEnv -> SnapShotId -> m()
takeSnapShot env p = tell $ Map.singleton p env 

type ClaferM = ClaferT Identity
-- Monad for using Clafer.
type ClaferT m = ErrorT ClaferErrs (WriterT SnapShots (StateT ClaferEnv m))

type ClaferErr = CErr ErrPos
type ClaferErrs = CErrs ErrPos

type ClaferSErr = CErr Span
type ClaferSErrs = CErrs Span

-- Possible errors that can occur when using Clafer
-- Generate errors using throwErr/throwErrs:
data CErr p =
  ClaferErr {  -- Generic error
    msg :: String
  } |
  ParseErr {   -- Error generated by the parser
    pos :: p,  -- Position of the error
    msg :: String
  } |
  SemanticErr { -- Error generated by semantic analysis
    pos :: p,
    msg :: String
  }
  deriving Show
  
-- Clafer keeps track of multiple errors.
data CErrs p =
  ClaferErrs {errs :: [CErr p]}
  deriving Show

instance Error (CErr p) where
  strMsg = ClaferErr
  
instance Error (CErrs p) where
  strMsg m = ClaferErrs [strMsg m]
  
data ErrPos =
  ErrPos {
    -- The fragment where the error occurred.
    fragId :: Int,
    -- Error positions are relative to their fragments.
    -- For example an error at (Pos 2 3) means line 2 column 3 of the fragment, not the entire model.
    fragPos :: Pos,
    -- The error position relative to the model.
    modelPos :: Pos
  }
  deriving Show
  

-- The full ErrPos requires lots of information that needs to be consistent. Every time we throw an error,
-- we need BOTH the (fragId, fragPos) AND modelPos. This makes it easier for developers using ClaferT so they
-- only need to provide part of the information and the rest is automatically calculated. The code using
-- ClaferT is more concise and less error-prone.
--
--   modelPos <- modelPosFromFragPos fragdId fragPos
--   throwErr $ ParserErr (ErrPos fragId fragPos modelPos)
--
--     vs
--
--   throwErr $ ParseErr (ErrFragPos fragId fragPos)
--
-- Hopefully making the error handling easier will make it more universal.
data PartialErrPos =
  -- Position relative to the start of the fragment. Will calculate model position automatically.
  -- fragId starts at 0
  -- The position is relative to the start of the fragment.
  ErrFragPos {
    pFragId :: Int,
    pFragPos :: Pos
  } |
  ErrFragSpan {
    pFragId :: Int,
    pFragSpan :: Span
  } |
  -- Position relative to the start of the complete model. Will calculate fragId and fragPos automatically.
  -- The position is relative to the entire complete model.
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
  toErrPos (ErrFragSpan frgId (PosSpan _ frgPos _)) = toErrPos $ ErrFragPos frgId frgPos -- Should never happen
  toErrPos (ErrModelPos modelPos') =
    do
      f <- getsEnv frags
      let fragSpans = zipWith Span (Pos 1 1 : f) f
      case findFrag modelPos' fragSpans of
        Just (frgId, Span fragStart _) -> return $ ErrPos frgId (modelPos' `minusPos` fragStart) modelPos'
        Just (frgId, PosSpan _ fragStart _) -> return $ ErrPos frgId (modelPos' `minusPos` fragStart) modelPos'
        Nothing -> error $ show modelPos' ++ " not within any frag spans: " ++ show fragSpans -- Indicates a bug in the Clafer translator
    where
    findFrag pos'' spans =
      find (inSpan pos'' . snd) (zip [0..] spans)
  toErrPos (ErrModelSpan (Span modelPos'' _)) = toErrPos $ ErrModelPos modelPos''
  toErrPos (ErrModelSpan (PosSpan _ modelPos'' _)) = toErrPos $ ErrModelPos modelPos'' -- Should never happen


class Throwable t where
  toErr :: t -> Monad m => ClaferT m ClaferErr
  
instance ClaferErrPos p => Throwable (CErr p) where
  toErr (ClaferErr mesg) = return $ ClaferErr mesg
  toErr err =
    do
      pos' <- toErrPos $ pos err
      return $ err{pos = pos'}
  
-- Throw many errors.
throwErrs :: (Monad m, Throwable t) => [t] -> ClaferT m a
throwErrs throws =
  do
    errors <- mapM toErr throws
    throwError $ ClaferErrs errors

-- Throw one error.
throwErr :: (Monad m, Throwable t) => t -> ClaferT m a
throwErr throw = throwErrs [throw]

-- Catch errors
catchErrs :: Monad m => ClaferT m a -> ([ClaferErr] -> ClaferT m a) -> ClaferT m a
catchErrs e h = e `catchError` (h . errs)

addPos :: Pos -> Pos -> Pos
addPos (Pos l c) (Pos 1 d) = Pos l (c + d - 1)    -- Same line
addPos (Pos l _) (Pos m d) = Pos (l + m - 1) d    -- Different line
addPos pos' (PosPos _ l c) = addPos pos' (Pos l c)
addPos (PosPos _ l c) pos' = addPos (Pos l c) pos'
minusPos :: Pos -> Pos -> Pos
minusPos (Pos l c) (Pos 1 d) = Pos l (c - d + 1)  -- Same line
minusPos (Pos l c) (Pos m _) = Pos (l - m + 1) c  -- Different line
minusPos pos' (PosPos _ l c) = minusPos pos' (Pos l c)
minusPos (PosPos _ l c) pos' = minusPos (Pos l c) pos'

inSpan :: Pos -> Span -> Bool
inSpan pos' (Span start end) = pos' >= start && pos' <= end
inSpan pos' (PosSpan _ s e)  = inSpan pos' (Span s e)

-- Get the ClaferEnv
getEnv :: Monad m => ClaferT m ClaferEnv
getEnv = lift $ lift  get

getsEnv :: Monad m => (ClaferEnv -> a) -> ClaferT m a
getsEnv = lift . lift . gets 

-- Modify the ClaferEnv
modifyEnv :: Monad m => (ClaferEnv -> ClaferEnv) -> ClaferT m ()
modifyEnv = lift . lift . modify

-- Set the ClaferEnv. Remember to set the env after every change.
putEnv :: Monad m => ClaferEnv -> ClaferT m ()
putEnv = lift . lift . put 


-- Uses the ErrorT convention:
--   Left is for error (a string containing the error message)
--   Right is for success (with the result)
runClaferTS :: Monad m => ClaferArgs -> ClaferT m a -> m ((Either [ClaferErr] a), SnapShots)
runClaferTS args' exec =
  mapLeft errs `liftM` evalStateT execErrorWriter env'
  where
  mapLeft :: (a -> c) -> (Either a b, SnapShots) -> (Either c b, SnapShots)
  mapLeft f ((Left l), s) = (Left (f l), s)
  mapLeft _ ((Right r), s) = (Right r, s)
  env' = makeEnv args'
  execErrorWriter = runWriterT $ runErrorT exec

runClaferT :: Monad m => ClaferArgs -> ClaferT m a -> m (Either [ClaferErr] a)
runClaferT args' exec = liftM fst $ runClaferTS args' exec

-- Convenience
runClafer :: ClaferArgs -> ClaferM a -> Either [ClaferErr] a
runClafer args' = runIdentity . runClaferT args' 

runClaferS :: ClaferArgs -> ClaferM a -> (Either [ClaferErr] a, SnapShots)
runClaferS args' = runIdentity . runClaferTS args'