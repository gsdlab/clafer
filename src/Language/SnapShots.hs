module Language.SnapShots (SnapShot(..), emptySnapShot, takeSnapshot) where

import Language.ClaferT

data SnapShots = SnapShots 	{ lexed :: ClaferEnv
							, layoutResolved :: ClaferEnv
							, parsed :: ClaferEnv
							, mapped :: ClaferEnv
							, desugared :: ClaferEnv
							, resolved :: ClaferEnv 
							, compiled :: ClaferEnv
							, generated :: ClaferEnv
							} deriving (Show, Eq)

emptySnapShot = SnapShots emptyEnv emptyrEnv emptyEnv emptyEnv emptyEnv emptyEnv emptyEnv emptyEnv


ssAdd :: snapShots -> ClaferEnv -> SnapShots
ssAdd s e
	| lexed s 			== emptyEnv	= SnapShots e emptyEnv emptyEnv emptyEnv emptyEnv emptyEnv emptyEnv emptyEnv
	| layoutResolved s 	== emptyEnv	= SnapShots (lexed s) e emptyEnv emptyEnv emptyEnv emptyEnv emptyEnv emptyEnv
	| pasred s 			== emptyEnv	= SnapShots (lexed s) (layoutResolved s) e emptyEnv emptyEnv emptyEnv emptyEnv emptyEnv
	| mapped s 			== emptyEnv = SnapShots (lexed s) (layoutResolved s) (pasred s) e emptyEnv emptyEnv emptyEnv emptyEnv
	| desugared s 		== emptyEnv = SnapShots (lexed s) (layoutResolved s) (pasred s) (mapped s) e emptyEnv emptyEnv emptyEnv
	| resolved s 		== emptyEnv = SnapShots (lexed s) (layoutResolved s) (pasred s) (mapped s) (desugared s) e emptyEnv emptyEnv
	| compiled s 		== emptyEnv = SnapShots (lexed s) (layoutResolved s) (parsed s) (mapped s) (desugared s) (resolved s) e emptyEnv
	| otherwise 					= SnapShots (lexed s) (layoutResolved s) (parsed s) (mapped s) (desugared s) (resolved s) (compiled s) e

takeSnapShot :: SnapShots
takeSnapShot = do
	env <- getEnv
	return $ ssAdd emptySnapShot env


{-
claferEnvSnapShot = snapShot

takeSnapshot = dp
	env <- getEnv
	return $ claferEnvSnapShot env
-}







