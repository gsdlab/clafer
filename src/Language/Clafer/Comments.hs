{-
 Copyright (C) 2012 Christopher Walker <http://gsd.uwaterloo.ca>

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

module Language.Clafer.Comments(getOptions, getFragments, getStats, getGraph, getComments) where

import Data.Maybe (fromMaybe)
import Data.List (stripPrefix)
import Language.Clafer.Front.Absclafer

type InputModel = String

getOptions :: InputModel -> String
getOptions model = case lines model of
  []    -> ""
  (s:_) -> fromMaybe "" $ stripPrefix "//# OPTIONS " s

getFragments :: InputModel -> [Int]
getFragments [] = []
getFragments xs = getFragments' (lines xs) 1
getFragments' :: [ InputModel ] -> Int -> [Int]
getFragments' [] _ = []
getFragments' ("//# FRAGMENT":xs) ln = ln:getFragments' xs (ln + 1)
getFragments' (_:xs) ln = getFragments' xs $ ln + 1

getStats :: InputModel -> [Int]
getStats [] = []
getStats xs = getStats' (lines xs) 1
getStats' :: [String] -> Int -> [Int]
getStats' [] _ = []
getStats' ("//# SUMMARY":xs) ln = ln:getStats' xs (ln + 1)
getStats' ("//# STATS":xs)   ln = ln:getStats' xs (ln + 1)
getStats' (_:xs) ln = getStats' xs $ ln + 1

getGraph :: InputModel -> [Int]
getGraph [] = []
getGraph xs = getGraph' (lines xs) 1
getGraph' :: [String] -> Int -> [Int]
getGraph' [] _ = []
getGraph' ("//# SUMMARY":xs) ln = ln:getGraph' xs (ln + 1)
getGraph' ("//# GRAPH":xs)   ln = ln:getGraph' xs (ln + 1)
getGraph' (_:xs) ln = getGraph' xs $ ln + 1

getComments :: InputModel -> [(Span, String)]
getComments input = getComments' input 1 1
getComments' :: String -> Integer -> Integer -> [(Span, String)]
getComments' []           _   _     = []
getComments' ('/':'/':xs) row col  = readLine ('/':'/':xs) (Pos row col)
getComments' ('/':'*':xs) row col  = readBlock ('/':'*':xs) (Pos row col)
getComments' ('\n':xs)    row _    = getComments' xs (row + 1) 1
getComments' (_:xs)       row col  = getComments' xs row $ col + 1

readLine :: String -> Pos -> [(Span, String)]
readLine    [] _                   = []
readLine    xs start@(Pos row col) = let comment = takeWhile (/= '\n') xs in 
                                                   ((Span start (Pos row (col + toInteger (length comment)))),
                                                    comment): getComments' (drop (length comment + 1) xs) (row + 1) 1


readBlock :: String -> Pos -> [(Span, String)]  
readBlock   xs start@(Pos row col) = let (end@(Pos row' col'), comment, rest) = readBlock' xs row col id in
                                      ((Span start end), comment):getComments' rest row' col'                                    
readBlock' :: String -> Integer
              -> Integer -> (String -> String)
              -> (Pos, String,String)
readBlock' ('*':'/':xs) row col comment = ((Pos row $ col + 2), comment "*/", xs)
readBlock' ('\n':xs)    row _   comment = readBlock' xs (row + 1) 1 (comment "\n" ++)
readBlock' (x:xs)       row col comment = readBlock' xs row (col + 1) (comment [x]++)
readBlock' []           row col comment = ((Pos row col), comment [], [])
