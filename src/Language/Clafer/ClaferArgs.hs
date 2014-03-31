{-# LANGUAGE DeriveDataTypeable #-}
{-
 Copyright (C) 2012-2014 Kacper Bak, Jimmy Liang <http://gsd.uwaterloo.ca>

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
{- | Command Line Arguments of the compiler.

See also <http://t3-necsis.cs.uwaterloo.ca:8091/ClaferTools/CommandLineArguments a model of the arguments in Clafer>,  including constraints and examples.
-}
module Language.Clafer.ClaferArgs where

import System.IO ( stdin, hGetContents )
import System.Console.CmdArgs
import System.Console.CmdArgs.Explicit hiding (mode)
import Data.List
import Data.Maybe
import Language.Clafer.SplitJoin
import Paths_clafer (version)
import Data.Version (showVersion)

-- | Type of output to be generated at the end of compilation
data ClaferMode = Alloy42 | Alloy | Xml | Clafer | Html | Graph | CVLGraph | Python | Choco
  deriving (Eq, Show, Ord, Data, Typeable)
instance Default ClaferMode where
  def = Alloy

-- | Scope inference strategy
data ScopeStrategy = None | Simple | Full
  deriving (Eq, Show, Data, Typeable)
instance Default ScopeStrategy where
  def = Simple

data ClaferArgs = ClaferArgs {
      mode :: [ ClaferMode ],
      console_output :: Bool,
      flatten_inheritance :: Bool,
      timeout_analysis :: Int,
      no_layout :: Bool,
      new_layout :: Bool,
      check_duplicates :: Bool,
      skip_resolver :: Bool,
      keep_unused :: Bool,
      no_stats :: Bool,
      schema :: Bool,
      validate :: Bool,
      noalloyruncommand :: Bool,
      tooldir :: FilePath,
      alloy_mapping :: Bool,
      self_contained :: Bool,
      add_graph :: Bool,
      show_references :: Bool,
      add_comments :: Bool,
      ecore2clafer :: Bool,
      scope_strategy :: ScopeStrategy,
      afm :: Bool,
      skip_goals :: Bool,
      meta_data :: Bool,
      file :: FilePath
    } deriving (Show, Data, Typeable)

clafer :: ClaferArgs
clafer = ClaferArgs {
  mode                = [] &= help "Generated output type. Available CLAFERMODEs are: 'alloy' (default, Alloy 4.1); 'alloy42' (Alloy 4.2); 'xml' (intermediate representation of Clafer model); 'clafer' (analyzed and desugared clafer model); 'html' (original model in HTML); 'graph' (graphical representation written in DOT language); 'cvlgraph' (cvl notation representation written in DOT language); 'python' (generates IR in python); 'choco' (Choco constraint programming solver). Multiple modes can be specified at the same time, e.g., '-m alloy -m html'." &= name "m",
  console_output      = def &= help "Output code on console." &= name "o",
  flatten_inheritance = def &= help "Flatten inheritance ('alloy' and 'alloy42' modes only)." &= name "i",
  timeout_analysis    = def &= help "Timeout for analysis.",
  no_layout           = def &= help "Don't resolve off-side rule layout." &= name "l",
  new_layout          = def &= help "Use new fast layout resolver (experimental)." &= name "nl",
  check_duplicates    = def &= help "Check duplicated clafer names in the entire model."  &= name "c",
  skip_resolver       = def &= help "Skip name resolution." &= name "f",
  keep_unused         = def &= help "Keep uninstantated abstract clafers ('alloy' and 'alloy42' modes only)." &= name "k",
  no_stats            = def &= help "Don't print statistics." &= name "s",
  schema              = def &= help "Show Clafer IR (intermediate representation) XML schema.",
  validate            = def &= help "Validate outputs of all modes. Uses 'tools/XsdCheck.class' for XML,  'tools/alloy4.jar' and 'tools/alloy4.2.jar' for Alloy models, and Clafer translator for desugared Clafer models. Use '--tooldir' to override the default location of these tools." &= name "v",
  noalloyruncommand   = def &= help "For usage with partial instances: Don't generate the alloy 'run show for ... ' command, and rename @.ref with unique names  ('alloy' and 'alloy42' modes only)." &= name "nr",
  tooldir             = def &= typDir &= help "Specify the tools directory ('validate' only). Default: 'tools/'.",
  alloy_mapping       = def &= help "Generate mapping to Alloy source code ('alloy' and 'alloy42' modes only)." &= name "a",
  self_contained      = def &= help "Generate a self-contained html document ('html' mode only).",
  add_graph           = def &= help "Add a graph to the generated html model ('html' mode only). Requires the \"dot\" executable to be on the system path.",
  show_references     = def &= help "Whether the links for references should be rendered. ('html' and 'graph' modes only)." &= name "sr",
  add_comments        = def &= help "Include comments from the source file in the html output ('html' mode only).",
  ecore2clafer        = def &= help "Translate an ECore model into Clafer.",
  scope_strategy      = def &= help "Use scope computation strategy: none, simple (default), or full." &= name "ss",
  afm                 = def &= help "Throws an error if the cardinality of any of the clafers is above 1." &= name "check-afm",
  skip_goals          = def &= help "Skip generation of Alloy code for goals. Useful for all tools working with standard Alloy." &= name "sg",
  meta_data           = def &= help "Generate a 'fully qualified name'-'least-partially-qualified name'-'unique ID' map ('.cfr-map'). In Alloy, Alloy42, and Choco modes, generate the scopes map ('.cfr-scope').",
  file                = def &= args   &= typ "FILE"
 } &= summary ("Clafer " ++ showVersion Paths_clafer.version) &= program "clafer"

mergeArgs :: ClaferArgs -> ClaferArgs -> ClaferArgs
mergeArgs a1 a2  = ClaferArgs (mode a1) (coMergeArg) 
  (mergeArg flatten_inheritance) (mergeArg timeout_analysis) 
  (mergeArg no_layout) (mergeArg new_layout) 
  (mergeArg check_duplicates) (mergeArg skip_resolver) 
  (mergeArg keep_unused) (mergeArg no_stats) (mergeArg schema)
  (mergeArg validate) (mergeArg noalloyruncommand) (toolMergeArg) 
  (mergeArg alloy_mapping) (mergeArg self_contained) 
  (mergeArg add_graph) (mergeArg show_references) 
  (mergeArg add_comments) (mergeArg ecore2clafer) 
  (mergeArg scope_strategy) (mergeArg afm) (mergeArg skip_goals) 
  (mergeArg meta_data) (mergeArg file)
  where
    coMergeArg :: Bool
    coMergeArg = if (r1 /= False) then r1 else 
      if (r2 /= False) then r2 else (null $ file a1)
         where r1 = console_output a1;r2 = console_output a2
    toolMergeArg :: String
    toolMergeArg = if (r1 /= "") then r1 else 
      if (r2 /= "") then r2 else "/tools"
      where r1 = tooldir a1;r2 = tooldir a2
    mergeArg :: (Default a, Eq a) => (ClaferArgs -> a) -> a
    mergeArg f = (\r -> if (r /= def) then r else f a2) $ f a1

mainArgs :: IO (ClaferArgs, String)
mainArgs = do
  args' <- cmdArgs clafer 
  model <- case file args' of
             "" -> hGetContents stdin
             f  -> readFile f
  let args'' = argsWithOPTIONS args' model
  -- Alloy should be the default mode but only if nothing else was specified
  -- cannot use [ Alloy ] as the default in the definition of `clafer :: ClaferArgs` since 
  -- Alloy will always be a mode in addition to the other specified modes (it will become mandatory)
  let args''' = if null $ mode args''
                then args''{mode = [ Alloy ]}
                else args''
  return $ (args''', model)

argsWithOPTIONS :: ClaferArgs -> String -> ClaferArgs
argsWithOPTIONS    args'         model   =
  let 
    firstLine = case lines model of
                 [] -> ""
                 (s:_) -> s
    options = fromMaybe "" $ stripPrefix "//# OPTIONS " firstLine
  in
    either (const args') (mergeArgs args' . cmdArgsValue) $
               process (cmdArgsMode clafer) $ Language.Clafer.SplitJoin.splitArgs options

defaultClaferArgs :: ClaferArgs
defaultClaferArgs = ClaferArgs [ def ] True False 0 False False False False False False False False False "tools/" False False False False False False Simple False False False ""
