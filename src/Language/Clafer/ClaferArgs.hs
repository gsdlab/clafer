{-# LANGUAGE DeriveDataTypeable #-}
{-
 Copyright (C) 2012-2026 Kacper Bak, Jimmy Liang <http://gsd.uwaterloo.ca>

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

See also <https://wiselab.uwaterloo.ca/modelwiki/ClaferTools/CommandLineArguments a model of the arguments in Clafer>,  including constraints and examples.
-}
module Language.Clafer.ClaferArgs where

import System.Console.CmdArgs
import System.Console.CmdArgs.Explicit hiding (mode)
import Data.List ( isPrefixOf )
import Language.Clafer.SplitJoin
import Paths_clafer (version)
import Data.Version (showVersion)


-- | Type of output to be generated at the end of compilation
data ClaferMode = AlloyLtl | Alloy | JSON | Clafer | Html | Graph | CVLGraph | Choco
  deriving (Eq, Show, Ord, Data, Typeable)
instance Default ClaferMode where
  def = Alloy

-- | Scope inference strategy
data ScopeStrategy = None | Simple
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
      validate :: Bool,
      tooldir :: FilePath,
      alloy_mapping :: Bool,
      self_contained :: Bool,
      add_graph :: Bool,
      show_references :: Bool,
      add_comments :: Bool,
      ecore2clafer :: Bool,
      trace_len :: Integer,
      scope_strategy :: ScopeStrategy,
      afm :: Bool,
      meta_data :: Bool,
      minint :: Maybe Integer,
      maxint :: Maybe Integer,
      decimal_digits :: Maybe Integer,
      imports :: [FilePath],
      import_root :: [FilePath],
      public_imports :: Bool,
      import_base :: String,
      file :: FilePath
    } deriving (Eq, Show, Data, Typeable)

clafer :: ClaferArgs
clafer = ClaferArgs {
  mode                = [] &= help "Generated output type. Available CLAFERMODEs are: 'alloy' (default, Alloy 6); 'json' (intermediate representation of Clafer model); 'clafer' (analyzed and desugared clafer model); 'html' (original model in HTML); 'graph' (graphical representation written in DOT language); 'cvlgraph' (cvl notation representation written in DOT language); 'choco' (Choco constraint programming solver). Multiple modes can be specified at the same time, e.g., '-m alloy -m html'." &= name "m",
  console_output      = def &= help "Output code on console." &= name "o",
  flatten_inheritance = def &= help "Flatten inheritance ('alloy' mode only)." &= name "i",
  timeout_analysis    = def &= help "Timeout for analysis.",
  no_layout           = def &= help "Don't resolve off-side rule layout." &= name "l",
  new_layout          = def &= help "Use new fast layout resolver (experimental)." &= name "nl",
  check_duplicates    = def &= help "Check duplicated clafer names in the entire model."  &= name "c",
  skip_resolver       = def &= help "Skip name resolution." &= name "f",
  keep_unused         = def &= help "Keep uninstantated abstract clafers ('alloy' mode only)." &= name "k",
  no_stats            = def &= help "Don't print statistics." &= name "s",
  validate            = def &= help "Validate outputs of all modes. Uses '<tooldir>/alloy6.2.0.jar' for Alloy models, '<tooldir>/chocosolver.jar' for Choco models, and Clafer translator for desugared Clafer models. Use '--tooldir' to override the default location ('.') of these tools." &= name "v",
  tooldir             = "." &= typDir &= help "Specify the tools directory ('validate' only). Default: '.' (current directory).",
  alloy_mapping       = def &= help "Generate mapping to Alloy source code ('alloy' mode only)." &= name "a",
  self_contained      = def &= help "Generate a self-contained html document ('html' mode only).",
  add_graph           = def &= help "Add a graph to the generated html model ('html' mode only). Requires the \"dot\" executable to be on the system path.",
  show_references     = def &= help "Whether the links for references should be rendered. ('html' and 'graph' modes only)." &= name "sr",
  add_comments        = def &= help "Include comments from the source file in the html output ('html' mode only).",
  ecore2clafer        = def &= help "Translate an ECore model into Clafer.",
  trace_len           = 10 &= help "Define the maximum trace length." &= name "tl",
  scope_strategy      = def &= help "Use scope computation strategy: none or simple (default)." &= name "ss",
  afm                 = def &= help "Throws an error if the cardinality of any of the clafers is above 1." &= name "check-afm",
  meta_data           = def &= help "Generate a 'fully qualified name'-'least-partially-qualified name'-'unique ID' map ('.cfr-map'). In Alloy and Choco modes, generate the scopes map ('.cfr-scope').",
  minint              = def &= help "Smallest integer value ('choco' mode only). Default: -128, chosen by chocosolver." &= typ "INT" &= explicit &= name "minint",
  maxint              = def &= help "Largest integer value ('choco' mode only). Default: 127, chosen by chocosolver." &= typ "INT" &= explicit &= name "maxint",
  decimal_digits      = def &= help "Number of fractional digits of decimals ('choco' mode only). Default: the most fractional digits of the model's decimal literals." &= typ "INT" &= explicit &= name "decimal-digits",
  imports             = def &= help "Compile the model with the model in FILE (a path or an http/https URL), which is compiled before it (and only once, if imported by several files). In '//# OPTIONS', FILE is relative to the model's folder or URL; options of the imported files are combined with the model's. Can be repeated." &= typFile &= explicit &= name "import",
  import_root         = def &= help "Allow only local imports inside DIR, after resolving '..' and symbolic links (command line only). Can be repeated; without it, any local file can be imported." &= typDir &= explicit &= name "import-root",
  public_imports      = def &= help "Allow only URL imports from public addresses, not from loopback, private, or link-local ones, without a proxy (command line only)." &= explicit &= name "public-imports",
  import_base         = def &= help "The URL from which the model's text was read: its imports are relative to the URL, and can only be URLs (command line only)." &= typ "URL" &= explicit &= name "import-base",
  file                = def &= args   &= typ "FILE"
 } &= summary ("Clafer " ++ showVersion Paths_clafer.version) &= program "clafer"

-- | The command line of the compiler, built once: cmdArgs reads the annotations of 'clafer'
--   (e.g., the names of the options) only the first time it is used, so the command line and
--   the @//# OPTIONS@ of the models must be parsed with this mode.
claferMode :: Mode (CmdArgs ClaferArgs)
claferMode = cmdArgsMode clafer
{-# NOINLINE claferMode #-}

-- | The arguments of an empty command line (the defaults).
claferDefaults :: ClaferArgs
claferDefaults = either error cmdArgsValue $ process claferMode []

-- | Merges the command line arguments (a1) with the options of the model (a2): an argument
--   given on the command line takes precedence, the imports of both are kept.
mergeArgs :: ClaferArgs -> ClaferArgs -> ClaferArgs
mergeArgs a1 a2  = ClaferArgs
  { mode = mergeArg mode
  , console_output = console_output a1 || console_output a2 || null (file a1)
  , flatten_inheritance = mergeArg flatten_inheritance
  , timeout_analysis = mergeArg timeout_analysis
  , no_layout = mergeArg no_layout
  , new_layout = mergeArg new_layout
  , check_duplicates = mergeArg check_duplicates
  , skip_resolver = mergeArg skip_resolver
  , keep_unused = mergeArg keep_unused
  , no_stats = mergeArg no_stats
  , validate = mergeArg validate
  , tooldir = mergeArg tooldir
  , alloy_mapping = mergeArg alloy_mapping
  , self_contained = mergeArg self_contained
  , add_graph = mergeArg add_graph
  , show_references = mergeArg show_references
  , add_comments = mergeArg add_comments
  , ecore2clafer = mergeArg ecore2clafer
  , trace_len = mergeArg trace_len
  , scope_strategy = mergeArg scope_strategy
  , afm = mergeArg afm
  , meta_data = mergeArg meta_data
  , minint = mergeArg minint
  , maxint = mergeArg maxint
  , decimal_digits = mergeArg decimal_digits
  , imports = imports a1 ++ filter (`notElem` imports a1) (imports a2)
  , import_root = mergeArg import_root
  , public_imports = mergeArg public_imports
  , import_base = mergeArg import_base
  , file = mergeArg file
  }
  where
    -- the command line's value, unless it is the default (an option not given)
    mergeArg :: Eq a => (ClaferArgs -> a) -> a
    mergeArg f = if f a1 /= f claferDefaults then f a1 else f a2

argsWithOPTIONS :: ClaferArgs -> String -> ClaferArgs
argsWithOPTIONS    args'         model   =
  if "//# OPTIONS " `isPrefixOf` model
  then either (const args') (mergeArgs args' . cmdArgsValue) $ -- merge wth command line arguments, which take precedence
          process claferMode $                    -- instantiate ClaferArgs record
            Language.Clafer.SplitJoin.splitArgs $ -- extract individual arguments
              drop 12 $                           -- strip "//# OPTIONS "
                takeWhile (/= '\n') model         -- get first line
  else args'

defaultClaferArgs :: ClaferArgs
defaultClaferArgs = ClaferArgs
  { mode = [ def ]
  , console_output = True
  , flatten_inheritance = False
  , timeout_analysis = 0
  , no_layout = False
  , new_layout = False
  , check_duplicates = False
  , skip_resolver = False
  , keep_unused = False
  , no_stats = False
  , validate = False
  , tooldir = "."
  , alloy_mapping = False
  , self_contained = False
  , add_graph = False
  , show_references = False
  , add_comments = False
  , ecore2clafer = False
  , trace_len = 10
  , scope_strategy = Simple
  , afm = False
  , meta_data = False
  , minint = Nothing
  , maxint = Nothing
  , decimal_digits = Nothing
  , imports = []
  , import_root = []
  , public_imports = False
  , import_base = ""
  , file = ""
  }
