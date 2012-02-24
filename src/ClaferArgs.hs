{-
 Copyright (C) 2012 Kacper Bak, Jimmy Liang <http://gsd.uwaterloo.ca>

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
{-# LANGUAGE DeriveDataTypeable #-}
module ClaferArgs where

import System.Console.CmdArgs
import System.Console.CmdArgs.Explicit hiding (mode)
import Data.List
import Data.Maybe
import Control.Monad
import SplitJoin

import Version

data ClaferMode = Alloy42 | Alloy | Xml | Clafer
  deriving (Eq, Show, Data, Typeable)

data ClaferArgs = ClaferArgs {
      mode :: Maybe ClaferMode,
      console_output :: Maybe Bool,
      flatten_inheritance :: Maybe Bool,
      timeout_analysis :: Maybe Int,
      no_layout :: Maybe Bool,
      new_layout :: Maybe Bool,
      check_duplicates :: Maybe Bool,
      force_resolver :: Maybe Bool,
      keep_unused :: Maybe Bool,
      no_stats :: Maybe Bool,
      schema :: Maybe Bool,
      validate :: Maybe Bool,
      tooldir :: Maybe FilePath,
      file :: FilePath
    } deriving (Show, Data, Typeable)

clafer = ClaferArgs {
  mode                = def &= help "Generated output type. Available modes: alloy (default); alloy42 (new Alloy version); xml (intermediate representation of Clafer model); clafer (analyzed and desugared clafer model)" &= name "m",
  console_output      = def &= help "Output code on console" &= name "o",
  flatten_inheritance = def &= help "Flatten inheritance" &= name "i",
  timeout_analysis    = def &= help "Timeout for analysis",
  no_layout           = def &= help "Don't resolve off-side rule layout" &= name "l",
  new_layout          = def &= help "Use new fast layout resolver (experimental)" &= name "nl",
  check_duplicates    = def &= help "Check duplicated clafer names",
  force_resolver      = def &= help "Force name resolution" &= name "f",
  keep_unused         = def &= help "Keep unused abstract clafers" &= name "k",
  no_stats            = def &= help "Don't print statistics" &= name "s",
  schema              = def &= help "Show Clafer XSD schema",
  validate            = def &= help "Validate output. Uses XsdCheck for XML, Alloy Analyzer for Alloy models, and Clafer translator for desugared Clafer models. Use --tooldir to specify where the binaries (XsdCheck.class, Alloy4.jar, Alloy4.2-rc.jar) are located.",
  tooldir             = def &= typDir &= help "Tools directory",
  file                = def &= args   &= typ "FILE"
 } &= summary ("Clafer " ++ version) &= program "clafer"

mainArgs = do
  args <- cmdArgs clafer
  model <- readFile $ file args
  let firstLine = case lines model of
               [] -> ""
               (s:_) -> s
  let options = fromMaybe "" $ stripPrefix "//# OPTIONS " firstLine
  return $ setDefArgs $
           either (\_ -> args) (\x -> mergeArgs args (cmdArgsValue x)) $
           process (cmdArgsMode clafer) $ SplitJoin.splitArgs options

-- merges console arguments with pragmas in clafer models.
-- Console arguments have higher priority.
mergeArgs args args'  = args' {
  mode                = mode args                `mplus` mode args',
  console_output      = console_output args      `mplus` console_output args',
  flatten_inheritance = flatten_inheritance args `mplus` flatten_inheritance args',
  timeout_analysis    = timeout_analysis args    `mplus` timeout_analysis args',
  no_layout           = no_layout args           `mplus` no_layout args',
  new_layout          = new_layout args          `mplus` new_layout args',
  check_duplicates    = check_duplicates args    `mplus` check_duplicates args',
  force_resolver      = force_resolver args      `mplus` force_resolver args',
  keep_unused         = keep_unused args         `mplus` keep_unused args',
  no_stats            = no_stats args            `mplus` no_stats args',
  schema              = schema args              `mplus` schema args',
  validate            = validate args            `mplus` validate args',
  tooldir             = tooldir args             `mplus` tooldir args',
  file                = file args}

-- default values for arguments (the lowest priority)
setDefArgs args = args {
  mode                = mode args                `mplus` Just Alloy,
  console_output      = console_output args      `mplus` Just def,
  flatten_inheritance = flatten_inheritance args `mplus` Just def,
  timeout_analysis    = timeout_analysis args    `mplus` Just def,
  no_layout           = no_layout args           `mplus` Just def,
  new_layout          = new_layout args          `mplus` Just def,
  check_duplicates    = check_duplicates args    `mplus` Just def,
  force_resolver      = force_resolver args      `mplus` Just def,
  keep_unused         = keep_unused args         `mplus` Just def,
  no_stats            = no_stats args            `mplus` Just def,
  schema              = schema args              `mplus` Just def,
  validate            = validate args            `mplus` Just def,
  tooldir             = tooldir args             `mplus` Just "tools/"}
