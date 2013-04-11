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
module Language.Clafer.Css where

header = "<!DOCTYPE html>\n<html>\n<head>\n<meta http-equiv=\"X-UA-Compatible\" content=\"IE=9\">\n"

css = unlines [ 
  ".identifier{}",
  ".keyword{font-weight:bold}",
  ".reference{}",
  ".code { background-color: lightgray; padding: 5px 5px 5px 5px; border: 1px solid darkgray; margin-bottom: 15px; ",
  "        font-family: Pragmata, Menlo, 'DejaVu LGC Sans Mono', 'DejaVu Sans Mono', Consolas, 'Everson Mono', 'Lucida Console', 'Andale Mono', 'Nimbus Mono L', 'Liberation Mono', FreeMono, 'Osaka Monospaced', Courier, 'New Courier', monospace; }",
  ".standalonecomment { color: green; font-style:italic }",
  ".inlinecomment { color: green; padding-left:20px; font-style:italic }",
  ".error{background-color: yellow; color: red }",
  ".indent{padding-left:20px}",
  "a[href$='Lookup failed'] {color: red}",
  "a[href$='Uid not found'] {color: red}",
  "a[href$='Ambiguous name'] {color: yellow}",
 "" ]
