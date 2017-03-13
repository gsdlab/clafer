{-# LANGUAGE RecordWildCards #-}
{-
 Copyright (C) 2012-2017 Kacper Bak <http://gsd.uwaterloo.ca>

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
module Language.Clafer.SplitJoin(splitArgs, joinArgs) where

import Data.Char
import Data.Maybe


-- | Given a sequence of arguments, join them together in a manner that could be used on
-- |  the command line, giving preference to the Windows @cmd@ shell quoting conventions.
-- | For an alternative version, intended for actual running the result in a shell, see "System.Process.showCommandForUser"
joinArgs :: [String] -> String
joinArgs = unwords . map f
    where
        f x = q ++ g x ++ q
            where
                hasSpace = any isSpace x
                q = ['\"' | hasSpace || null x]

                g ('\\':'\"':xs') = '\\':'\\':'\\':'\"': g xs'
                g "\\" | hasSpace = "\\\\"
                g ('\"':xs') = '\\':'\"': g xs'
                g (x':xs') = x' : g xs'
                g [] = []


data State = Init -- either I just started, or just emitted something
           | Norm -- I'm seeing characters
           | Quot -- I've seen a quote

-- | Given a string, split into the available arguments. The inverse of 'joinArgs'.
splitArgs :: String -> [String]
splitArgs = join . f Init
    where
        -- Nothing is start a new string
        -- Just x is accumulate onto the existing string
        join :: [Maybe Char] -> [String]
        join [] = []
        join xs = map fromJust a : join (drop 1 b)
            where (a,b) = break isNothing xs

        f Init (x:xs) | isSpace x = f Init xs
        f Init "\"\"" = [Nothing]
        f Init "\"" = [Nothing]
        f Init xs = f Norm xs
        f m ('\"':'\"':'\"':xs) = Just '\"' : f m xs
        f m ('\\':'\"':xs) = Just '\"' : f m xs
        f m ('\\':'\\':'\"':xs) = Just '\\' : f m ('\"':xs)
        f Norm ('\"':xs) = f Quot xs
        f Quot ('\"':'\"':xs) = Just '\"' : f Norm xs
        f Quot ('\"':xs) = f Norm xs
        f Norm (x:xs) | isSpace x = Nothing : f Init xs
        f m (x:xs) = Just x : f m xs
        f _ [] = []
