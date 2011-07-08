{-
 This file is part of the Clafer Translator (clafer).

 Copyright (C) 2010 Kacper Bak <http://gsd.uwaterloo.ca/kbak>

 clafer is free software: you can redistribute it and/or modify
 it under the terms of the GNU Lesser General Public License as published by
 the Free Software Foundation, either version 3 of the License, or
 (at your option) any later version.

 clafer is distributed in the hope that it will be useful,
 but WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 GNU Lesser General Public License for more details.

 You should have received a copy of the GNU Lesser General Public License
 along with clafer. (See files COPYING and COPYING.LESSER.)  If not,
 see <http://www.gnu.org/licenses/>.
-}
module Front.LayoutResolver where

-- very simple layout resolver
import Control.Monad.State

import Front.Lexclafer
import Data.Maybe

data LayEnv = LayEnv {
      level :: Int,
      levels :: [Int],
      input :: String,
      output :: String,
      brCtr :: Int
    } deriving Show

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
    when (c' `elem` ['[', ']','{', '}']) $ void $ handleIndent c'
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
