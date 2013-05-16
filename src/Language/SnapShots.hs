module Language.SnapShots (SnapShots(..), emptySnapShots,getSnapShots, putSnapShots) where

import Control.Monad.Error
import Control.Monad.State
import Language.ClaferT

data SnapShots = SnapShots 	{ lexed :: ClaferEnv
							, layoutResolved :: ClaferEnv
							, parsed :: ClaferEnv
							, mapped :: ClaferEnv
							, desugared :: ClaferEnv
							, foundDuplicates :: ClaferEnv
							, resolved :: ClaferEnv 
							, transformed :: ClaferEnv
							, scopeAnalizaed :: ClaferEnv
							, compiled :: ClaferEnv
							, generated :: ClaferEnv
							} deriving (Show, Eq)

emptySnapShots = SnapShots emptyEnv emptyEnv emptyEnv emptyEnv emptyEnv emptyEnv emptyEnv emptyEnv emptyEnv emptyEnv emptyEnv

type ClaferST m = ErrorT ClaferErrs (StateT SnapShots m)

getSnapShots :: Monad m => ClaferST m SnapShots
getSnapShots = get 

putSnapShots :: Monad m => SnapShots -> ClaferST m ()
putSnapShots = put



sAdd :: SnapShots -> ClaferEnv -> SnapShots
sAdd s e
	| lexed s 			== emptyEnv	= s {lexed = e}
	| layoutResolved s 	== emptyEnv	= s {layoutResolved = e}
	| parsed s 			== emptyEnv = s {parsed = e}
	| mapped s 			== emptyEnv = s {mapped = e}
	| desugared s 		== emptyEnv = s {desugared = e}
	| foundDuplicates s == emptyEnv = s {foundDuplicates = e}
	| resolved s 		== emptyEnv = s {resolved = e}
	| transformed s 	== emptyEnv = s {transformed = e}
	| scopeAnalizaed s	== emptyEnv	= s {scopeAnalizaed = e}
	| compiled s 		== emptyEnv = s {compiled = e}
	| otherwise						= s {generated = e}


takeSnapShot :: Monad m => ClaferST m ()
takeSnapShot = 
	do
		oldSnapShots <- getSnapShots
		--env <- getEnv
		newSnapShots <- return $ sAdd oldSnapShots emptyEnv
		putSnapShots newSnapShots

{-
takeSnapshot = 	getSnapShots >>= (\oldSnapShots ->
				getEnv >>= (\env ->
				(return $ sAdd oldSnapShots env) >>= (\newSnapShots ->
				putSnapShots newSnapShots)))

takeSnapshot = 	getSnapShots >>= (\oldSnapShots -> getEnv >>= (\env -> (return $ sAdd oldSnapShots env) >>= (\newSnapShots -> putSnapShots newSnapShots)))
-}	