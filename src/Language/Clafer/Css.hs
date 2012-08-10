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

header = "<!DOCTYPE html>\n<html>\n<head>\n<meta http-equiv=\"X-UA-Compatible\" content=\"IE=9\" />\n"

css = unlines [ "<style>",
  "body { font-size: 18px }",
  ".identifier{}",
  ".keyword{font-weight:bold}",
  ".reference{}",
  ".code { background-color: lightgray; font-size: 18px }",
  ".standalonecomment { color: green; font-style:italic }",
  ".inlinecomment { color: green; float:right; font-style:italic }",
  ".error{background-color: Yellow; color: DarkRed }",
  ".l0{}",
  ".l1{padding-left:20px}",
  ".l2{padding-left:40px}",
  ".l3{padding-left:60px}",
  ".l4{padding-left:80px}",
  ".l5{padding-left:100px}",
  ".l6{padding-left:120px}",
  ".l7{padding-left:140px}",
  ".l8{padding-left:160px}",
  ".l9{padding-left:180px}",
  ".l10{padding-left:200px}",
  ".l11{padding-left:220px}",
  ".l12{padding-left:240px}",
  ".l13{padding-left:260px}",
  ".l14{padding-left:280px}",
  ".l15{padding-left:300px}",
  ".l16{padding-left:320px}",
  ".l17{padding-left:340px}",
  ".l18{padding-left:360px}",
  ".l19{padding-left:380px}",
  ".l20{padding-left:400px}",
  "a[href$='Lookup failed'] {color: red}",
  "a[href$='Uid not found'] {color: red}",
  "a[href$='Ambiguous name'] {color: yellow}",
  "</style>"]
