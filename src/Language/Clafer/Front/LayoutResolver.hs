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
import Control.Monad
import Language.Clafer.Common

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

getToken (ExToken t) = t

layoutOpen  = "{"
layoutClose = "}"

resolveLayout :: [Token] -> [Token]
resolveLayout xs = adjust $ resolve (LEnv [1] Nothing) $ addNewLines xs

resolve :: LEnv -> [ExToken] -> [Token]
resolve (LEnv st _) [] = replicate (length st - 1) dedent
resolve (LEnv st _) ((NewLine lastNl):ts) = resolve (LEnv st (Just lastNl)) ts
resolve env@(LEnv st lastNl) (t:ts)
  | isJust lastNl && parLev > 0 = t' : resolve env ts
  | isJust lastNl && newLev > head st = indent : t' : resolve
                                        (LEnv (newLev : st) Nothing) ts
  | isJust lastNl && newLev == head st = t' : resolve (LEnv st Nothing) ts
  | isJust lastNl = replicate (length st - length st') dedent ++ [t'] ++
    resolve (LEnv st' Nothing) ts
  | otherwise = t' : resolve env ts
  where
  t' = getToken t
  (newLev, parLev) = fromJust lastNl
  st' = dropWhile (newLev <) st

indent = sToken (Pn 0 0 0) "{"
dedent = sToken (Pn 0 0 0) "}"

toToken (NewLine _) = []
toToken (ExToken t) = [t]

isExTokenIn l (ExToken t) = isTokenIn l t
isExTokenIn _ _ = False


isNewLine :: Token -> Token -> Bool
isNewLine t1 t2 = line t1 < line t2

-- | Add to the global and column positions of a token.
--   The column position is only changed if the token is on
--   the same line as the given position.
incrGlobal :: Position -- ^ If the token is on the same line
                       --   as this position, update the column position.
           -> Int      -- ^ Number of characters to add to the position.
           -> Token -> Token
incrGlobal (Pn _ l0 _) i (PT (Pn g l c) t) =
  if l /= l0 then PT (Pn (g + i) l c) t
             else PT (Pn (g + i) l (c + i)) t
incrGlobal _ _ p = error $ "cannot add token at " ++ show p

-- | Create a symbol token.
sToken :: Position -> String -> Token
sToken p s = PT p (TS s i)
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
      _ -> error $ "not a reserved word: " ++ show s

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

isBracketOpen = isTokenIn ["["]

-- | Check if a token is the layout close token.
isLayoutClose :: Token -> Bool
isLayoutClose = isTokenIn [layoutClose]

isBracketClose = isTokenIn ["]"]

-- | Get the number of characters in the token.
tokenLength :: Token -> Int
tokenLength t = length $ prToken t

-- data ExToken = NewLine (Int, Int) | ExToken Token
addNewLines :: [Token] -> [ExToken]
addNewLines = addNewLines' 0

addNewLines' :: Int -> [Token] -> [ExToken]
addNewLines' 0 (t:[])     = [ExToken t]
addNewLines' n (t:[])
  | n == 0 && isBracketClose t = [ExToken t]
  | otherwise                  = error $ "']' bracket missing" ++ show n ++ show t
addNewLines' n (t0:t1:ts)
  | isNewLine t0 t1 && isBracketOpen t1 =
    ExToken t0 : NewLine (column t1, n) : addNewLines' (n + 1) (t1:ts)
  | isNewLine t0 t1 && isBracketClose t1 =
    ExToken t0 : NewLine (column t1, n) : addNewLines' (n - 1) (t1:ts)
  | isLayoutOpen t1  || isBracketOpen t1 =
    ExToken t0 : addNewLines' (n + 1) (t1:ts)
  | isLayoutClose t1 || isBracketClose t1 =
    ExToken t0 : addNewLines' (n - 1) (t1:ts)
  | isNewLine t0 t1  = ExToken t0 : NewLine (column t1, n) : addNewLines' n (t1:ts)
  | otherwise        = ExToken t0 : addNewLines' n (t1:ts)

adjust [] = []
adjust (t:[]) = [t]
adjust (t:ts) = t : adjust (updToken (t:ts))

updToken (t0:t1:ts)
  | isLayoutOpen t1 || isLayoutClose t1 = addToken (nextPos t0) sym ts
  | otherwise = (t1:ts)
  where
  sym = if isLayoutOpen t1 then "{" else "}"

-- | Get the position immediately to the right of the given token.
nextPos :: Token -> Position 
nextPos t = Pn (g + s) l (c + s + 1) 
  where Pn g l c = position t
        s = tokenLength t

-- | Insert a new symbol token at the begninning of a list of tokens.
addToken :: Position -- ^ Position of the new token.
         -> String   -- ^ Symbol in the new token.
         -> [Token]  -- ^ The rest of the tokens. These will have their
                     --   positions updated to make room for the new token.
         -> [Token]
addToken p s ts = sToken p s : map (incrGlobal p (length s)) ts

resLayout :: String -> String
resLayout input = 
  reverse $ output $ execState resolveLayout' $ LayEnv 0 [] input' [] 0
  where
  input' = unlines $ filter (/= "") $ lines input


resolveLayout' = do
  stop <- isEof
  when (not stop) $ do
    c  <- getc
    c' <- handleIndent c
    emit c'
    resolveLayout'

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


emit c = modify (\e -> e {output = c : output e})


readC n = if n > 0 then getc else return '\n'


eatSpaces = do
  cs <- gets input
  let (sp, rest) = break (/= ' ') cs
  modify (\e -> e {input = rest, output = sp ++ output e})
  ctr <- gets brCtr
  if ctr > 0 then gets level else return $ length sp


emitIndent n = do
  lev <- gets level  
  when (n > lev) $ do
    ctr <- gets brCtr
    when (ctr < 1) $ do
      emit '{'
    modify (\e -> e {level = n, levels = lev : levels e})


emitDedent n = do
  lev <- gets level
  when (n < lev) $ do
    ctr <- gets brCtr
    when (ctr < 1) $ emit '}'
    modify (\e -> e {level = head $ levels e, levels = tail $ levels e})
    emitDedent n


isEof = null `liftM` (gets input)


getc = do
  c <- gets (head.input)
  modify (\e -> e {input = tail $ input e})
  return c

revertLayout :: String -> String
revertLayout input = unlines $ revertLayout' (lines input) 0 

revertLayout' :: [String] -> Int -> [String]
revertLayout' []             indent = []
revertLayout' ([]:xss)       indent = revertLayout' xss indent
revertLayout' (('{':xs):xss) indent = (replicate indent' ' ' ++ xs):revertLayout' xss indent'
                                    where indent' = indent + 2
revertLayout' (('}':xs):xss) indent = (replicate indent' ' ' ++ xs):revertLayout' xss indent'
                                    where indent' = indent - 2
revertLayout' (xs:xss)       indent = (replicate indent ' ' ++ xs):revertLayout' xss indent
