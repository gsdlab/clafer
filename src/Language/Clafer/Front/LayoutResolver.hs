{-# LANGUAGE FlexibleContexts #-}
{-
 Copyright (C) 2012 Kacper Bak, Christopher Walker <http://gsd.uwaterloo.ca>

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
module Language.Clafer.Front.LayoutResolver where

-- very simple layout resolver
import Control.Monad.State
import Data.Functor.Identity (Identity)
import Language.Clafer.Common
import Language.ClaferT

import Language.Clafer.Front.Lexclafer
import Data.Maybe

data LayEnv = LayEnv {
      level :: Int,
      levels :: [Int],
      input :: String,
      output :: String,
      brCtr :: Int
    } deriving Show


-- ident level of new line, current level or parenthesis
type LastNl = (Int, Int)

type Position = Posn

data ExToken = NewLine LastNl | ExToken Token deriving Show

-- ident level stack, last new line
data LEnv = LEnv [Int] (Maybe LastNl)

getToken :: (Monad m) => ExToken -> ClaferT m Token
getToken (ExToken t) = return t
getToken (NewLine (x, y)) = throwErr $ ParseErr (ErrPos 0 fPos fPos) $ "LayoutResolver.getToken: Cannot get ExToken NewLine"-- this shoud never happen
  where
    fPos = Pos (fromIntegral x) (fromIntegral y)

layoutOpen :: String
layoutOpen  = "{"
layoutClose :: String
layoutClose = "}"

resolveLayout :: (Monad m) => [Token] -> ClaferT m  [Token]
resolveLayout xs = addNewLines xs >>= (resolve (LEnv [1] Nothing)) >>= adjust

resolve :: (Monad m) => LEnv -> [ExToken] -> ClaferT m [Token]
resolve (LEnv st _) [] = return $ replicate (length st - 1) dedent
resolve (LEnv st _) ((NewLine lastNl):ts) = resolve (LEnv st (Just lastNl)) ts
resolve env@(LEnv st lastNl) (t:ts)
  | isJust lastNl && parLev > 0 = do
    r <- resolve env ts
    t' >>= return . (:r)
  | isJust lastNl && newLev > head st = do
    r <- resolve (LEnv (newLev : st) Nothing) ts
    t' >>=  return . (indent:) . (:r)
  | isJust lastNl && newLev == head st = do
    r <- resolve (LEnv st Nothing) ts
    t' >>= return . (:r)
  | isJust lastNl = do
    r <- resolve (LEnv st' Nothing) ts
    t' >>= return . (replicate (length st - length st') dedent ++) . (:r)
  | otherwise = do
    r <- resolve env ts
    t' >>= return . (:r)
  where
  t' = getToken t
  (newLev, parLev) = fromJust lastNl
  st' = dropWhile (newLev <) st

indent :: Token
indent = PT (Pn 0 0 0) (TS "{" $ tokenLookup "{")
dedent :: Token
dedent = PT (Pn 0 0 0) (TS "}" $ tokenLookup "}") 

toToken :: ExToken -> [Token]
toToken (NewLine _) = []
toToken (ExToken t) = [t]

isExTokenIn :: [String] -> ExToken -> Bool
isExTokenIn l (ExToken t) = isTokenIn l t
isExTokenIn _ _ = False


isNewLine :: Token -> Token -> Bool
isNewLine t1 t2 = line t1 < line t2

-- | Add to the global and column positions of a token.
--   The column position is only changed if the token is on
--   the same line as the given position.
incrGlobal :: (Monad m) => Position -- ^ If the token is on the same line
                       --   as this position, update the column position.
           -> Int      -- ^ Number of characters to add to the position.
           -> Token -> ClaferT m Token
incrGlobal (Pn _ l0 _) i (PT (Pn g l c) t) =
  return $ if l /= l0 then PT (Pn (g + i) l c) t
             else PT (Pn (g + i) l (c + i)) t
incrGlobal _ _ (Err (Pn z x y)) = do
  env <- getEnv
  let claferModel = lines $ unlines $ modelFrags env
  throwErr $ ParseErr (ErrPos z fPos fPos) $ "Cannot add token at '" ++ (take y $ claferModel !! (x-1)) ++ "'"
  where
    fPos = Pos (fromIntegral x) (fromIntegral y)


tokenLookup :: String -> Int
tokenLookup s = i
  where
    i = case s of
      "!" -> 1
      "!=" -> 2
      "#" -> 3
      "&" -> 4
      "&&" -> 5
      "(" -> 6
      ")" -> 7
      "*" -> 8
      "+" -> 9
      "++" -> 10
      "," -> 11
      "-" -> 12
      "--" -> 13
      "->" -> 14
      "->>" -> 15
      "." -> 16
      ".." -> 17
      "/" -> 18
      ":" -> 19
      ":=" -> 20
      ":>" -> 21
      ";" -> 22
      "<" -> 23
      "<:" -> 24
      "<<" -> 25
      "<=" -> 26      
      "<=>" -> 27
      "=" -> 28
      "=>" -> 29
      ">" -> 30
      ">=" -> 31
      ">>" -> 32
      "?" -> 33
      "[" -> 34
      "\\" -> 35
      "]" -> 36
      "`" -> 37
      "abstract" -> 38
      "all" -> 39
      "disj" -> 40
      "else" -> 41
      "enum" -> 42
      "if" -> 43
      "in" -> 44
      "lone" -> 45
      "max" -> 46
      "min" -> 47
      "mux" -> 48
      "no" -> 49
      "not" -> 50
      "one" -> 51
      "opt" -> 52
      "or" -> 53
      "some" -> 54
      "sum" -> 55       
      "then" -> 56
      "xor" -> 57
      "{" -> 58
      "|" -> 59
      "||" -> 60
      "}" -> 61
      _ -> 0

-- | Get the position of a token.
position :: Token -> Position
position t = case t of
  PT p _ -> p
  Err p -> p

-- | Get the line number of a token.
line :: Token -> Int
line t = case position t of Pn _ l _ -> l

-- | Get the column number of a token.
column :: Token -> Int
column t = case position t of Pn _ _ c -> c

-- | Check if a token is one of the given symbols.
isTokenIn :: [String] -> Token -> Bool
isTokenIn ts t = case t of
  PT _ (TS r _) | elem r ts -> True
  _ -> False

-- | Check if a token is the layout open token.
isLayoutOpen :: Token -> Bool
isLayoutOpen = isTokenIn [layoutOpen]

isBracketOpen :: Token -> Bool
isBracketOpen = isTokenIn ["["]

-- | Check if a token is the layout close token.
isLayoutClose :: Token -> Bool
isLayoutClose = isTokenIn [layoutClose]

isBracketClose :: Token -> Bool
isBracketClose = isTokenIn ["]"]

-- | Get the number of characters in the token.
tokenLength :: Token -> Int
tokenLength t = length $ prToken t

-- data ExToken = NewLine (Int, Int) | ExToken Token
addNewLines :: (Monad m) => [Token] -> ClaferT m [ExToken]
addNewLines []    = return []
addNewLines ts@(t:_) = addNewLines' (if isBracketOpen t then 1 else 0) ts

addNewLines' :: (Monad m) => Int -> [Token] -> ClaferT m [ExToken]
addNewLines' _ []                     = return []
addNewLines' 0 (t:[])                 = return [ExToken t]
addNewLines' _ ((PT (Pn z x y) t):[]) = throwErr $ ParseErr (ErrPos z fPos fPos) $ "']' bracket missing for (" ++ show t ++ ")"
  where
    fPos = (Pos (fromIntegral x) (fromIntegral y))
addNewLines' n (t0:t1:ts)
  | isNewLine t0 t1 && isBracketOpen t1 =
    addNewLines' (n + 1) (t1:ts) >>= (return . (ExToken t0:) . (NewLine (column t1, n):))
  | isNewLine t0 t1 && isBracketClose t1 =
    addNewLines' (n - 1) (t1:ts) >>= (return . (ExToken t0:) . (NewLine (column t1, n):))
  | isLayoutOpen t1  || isBracketOpen t1 =
    addNewLines' (n + 1) (t1:ts) >>= (return . (ExToken t0:))
  | isLayoutClose t1 || isBracketClose t1 =
    addNewLines' (n - 1) (t1:ts) >>= (return . (ExToken t0:)) 
  | isNewLine t0 t1  = addNewLines' n (t1:ts) >>= (return . (ExToken t0:) . (NewLine (column t1, n):)) 
  | otherwise        = addNewLines' n (t1:ts) >>= (return . (ExToken t0:)) 
addNewLines' _ _ = throwErr (ClaferErr "Function addNewLines' from LayoutResolver was given invalid arguments" :: CErr Span) -- This should never happen!


adjust :: (Monad m) => [Token] -> ClaferT m [Token]
adjust [] = return []
adjust (t:[]) = return [t]
adjust (t:ts) = ((updToken (t:ts)) >>= adjust) >>= (return . (t:))

updToken :: (Monad m) => [Token] -> ClaferT m [Token]
updToken (t0:t1:ts)
  | isLayoutOpen t1 || isLayoutClose t1 = addToken (nextPos t0) sym ts
  | otherwise = return (t1:ts)
  where
  sym = if isLayoutOpen t1 then "{" else "}"
  -- | Get the position immediately to the right of the given token.
  nextPos :: Token -> Position 
  nextPos t = Pn (g + s) l (c + s + 1) 
    where Pn g l c = position t
          s = tokenLength t
updToken [] = return []
updToken (t:ts) = return (t:ts)

-- | Insert a new symbol token at the begninning of a list of tokens.
addToken :: (Monad m) => Position -- ^ Position of the new token.
         -> String   -- ^ Symbol in the new token.
         -> [Token]  -- ^ The rest of the tokens. These will have their
                     --   positions updated to make room for the new token.
         -> ClaferT m [Token]
addToken p@(Pn z x y) s ts = do
  when (i==0) $ throwErr $ ParseErr (ErrPos z fPos fPos) $ "not a reserved word: " ++ show s
  (>>= (return . (PT p (TS s i):))) $ mapM (incrGlobal p (length s)) ts
  where
    fPos = Pos (fromIntegral x) (fromIntegral y)
    i = tokenLookup s

resLayout :: String -> String
resLayout input' = 
  reverse $ output $ execState resolveLayout' $ LayEnv 0 [] input'' [] 0
  where
  input'' = unlines $ filter (/= "") $ lines input'


resolveLayout' :: StateT LayEnv Identity ()
resolveLayout' = do
  stop <- isEof
  when (not stop) $ do
    c  <- getc
    c' <- handleIndent c
    emit c'
    resolveLayout'

handleIndent :: Char -> StateT LayEnv Identity Char
handleIndent c = case c of
  '\n' -> do
    emit c
    n  <- eatSpaces
    c' <- readC n
    emitIndent n
    emitDedent n
    when (c' `elem` ['[', ']','{', '}']) $ voidf $ handleIndent c'
    return c'
  '[' -> do
    modify (\e -> e {brCtr = brCtr e + 1})
    return c
  '{' -> do
    modify (\e -> e {brCtr = brCtr e + 1})
    return c
  ']' -> do
    modify (\e -> e {brCtr = brCtr e - 1})
    return c
  '}' -> do
    modify (\e -> e {brCtr = brCtr e - 1})
    return c
  _ ->  return c


emit :: MonadState LayEnv m => Char -> m ()
emit c = modify (\e -> e {output = c : output e})


readC :: (Num a, Ord a) => a -> StateT LayEnv Identity Char
readC n = if n > 0 then getc else return '\n'


eatSpaces :: StateT LayEnv Identity Int
eatSpaces = do
  cs <- gets input
  let (sp, rest) = break (/= ' ') cs
  modify (\e -> e {input = rest, output = sp ++ output e})
  ctr <- gets brCtr
  if ctr > 0 then gets level else return $ length sp


emitIndent :: MonadState LayEnv m => Int -> m ()
emitIndent n = do
  lev <- gets level  
  when (n > lev) $ do
    ctr <- gets brCtr
    when (ctr < 1) $ do
      emit '{'
    modify (\e -> e {level = n, levels = lev : levels e})


emitDedent :: MonadState LayEnv m => Int -> m ()
emitDedent n = do
  lev <- gets level
  when (n < lev) $ do
    ctr <- gets brCtr
    when (ctr < 1) $ emit '}'
    modify (\e -> e {level = head $ levels e, levels = tail $ levels e})
    emitDedent n


isEof :: StateT LayEnv Identity Bool
isEof = null `liftM` (gets input)


getc :: StateT LayEnv Identity Char
getc = do
  c <- gets (head.input)
  modify (\e -> e {input = tail $ input e})
  return c

revertLayout :: String -> String
revertLayout input' = unlines $ revertLayout' (lines input') 0 

revertLayout' :: [String] -> Int -> [String]
revertLayout' []             _ = []
revertLayout' ([]:xss)       i = revertLayout' xss i
revertLayout' (('{':xs):xss) i = (replicate i' ' ' ++ xs):revertLayout' xss i'
                                    where i' = i + 2
revertLayout' (('}':xs):xss) i = (replicate i' ' ' ++ xs):revertLayout' xss i'
                                    where i' = i - 2
revertLayout' (xs:xss)       i = (replicate i ' ' ++ xs):revertLayout' xss i
