# Clafer


v0.4.0

[Clafer](http://clafer.org) is a general-purpose lightweight structural modeling language developed by
[GSD Lab](http://gsd.uwaterloo.ca/), [University of Waterloo](http://uwaterloo.ca), and
[MODELS](http://www.itu.dk/research/models/) group at [IT University of Copenhagen](http://www.itu.dk/).
Clafer can be used for modeling of static hierarchical structures but has no support for modeling the change of the structures over time (behavior).
The main goal of Clafer is to make modeling more accessible to a wider range of users and domains.

There are many possible applications of Clafer; however, three are prominent:

1. *Product-Line Modeling* - aims at representing and managing commonality and variability of assets in product lines and creating and verifying product configurations.
Clafer naturally supports multi-staged configuration.

2. *Multi-Objective Product Optimization* - aims at finding a set of products in a given product line that are optimal with respect to a set of objectives.
Clafer multi-objective optimizer generates a Pareto front of optimal product configurations.

3. *Domain Modeling* - aims at improving the understanding of the problem domain in the early stages of software development and determining the requirements with fewer defects.
This is also known as *Concept Modeling* or *Ontology Modeling*.

# Clafer Compiler


Clafer compiler provides a reference language implementation.
It translates models in Clafer to other formats (e.g., Alloy, JSON, Python, JS, HTML, DOT) to allow for reasoning and processing with existing tools (Alloy Analyzer, Choco3, and Z3 SMT solver).

Currently, the compiler is used by

* Backends
  * Alloy-based Instance Generator ([ClaferIG](https://github.com/gsdlab/claferIG)),
  * Choco3-based Instance Generator and Multi-Objective Optimizer ([chocosolver](https://github.com/gsdlab/chocosolver), [ClaferChocoIG](https://github.com/gsdlab/ClaferChocoIG)), and
  * Z3-based Instance Generator and Multi-Objective Optimizer ([ClaferSMT](https://github.com/gsdlab/claferSMT)),
* Web Frontends
  * Clafer Integrated Development Environment ([ClaferIDE](https://github.com/gsdlab/claferIDE)),
  * Clafer Configurator ([ClaferConfigurator](https://github.com/gsdlab/ClaferConfigurator)),
  * Multi-Objective [Visualizer and Explorer](https://github.com/gsdlab/ClaferMooVisualizer), and
  * Clafer Wiki ([ClaferWiki](https://github.com/gsdlab/claferwiki)).

## Contributors

* [Kacper Bak](http://gsd.uwaterloo.ca/kbak), Original developer.
* [Jimmy Liang](http://gsd.uwaterloo.ca/jliang), Main developer.
* [Michał Antkiewicz](http://gsd.uwaterloo.ca/mantkiew), Requirements, development, architecture, testing, technology transfer.
* [Ed Zulkoski](http://gsd.uwaterloo.ca/ezulkosk), Python IR Generator.
* Luke Michael Brown, co-op student May-Aug 2013. Many improvements.
* Paulius Juodisius, [customized BNFC generator](https://github.com/juodaspaulius/bnfc) and layout resolver.
* [Rafael Olaechea](http://gsd.uwaterloo.ca/rolaechea), Multi-Objective Optimization extensions.

## Getting the Clafer Compiler

Clafer can be installed from a binary distribution (preferred), from Hackage, and from the source code.

### Dependencies for running

Regardless of the installation method, the following are

Optional:

* [Java Platform (JDK)](http://www.oracle.com/technetwork/java/javase/downloads/index.html) v8+, 32bit
  * needed only for running Alloy validation
* [Alloy4.1 and/or Alloy4.2](http://alloy.mit.edu/alloy/download.html)
  * needed only for Alloy output validation
* [GraphViz](http://graphviz.org/)
  * the program `dot` is needed only in the `html` mode for SVG graph generation

### Installation from binaries

Binary distributions of the release 0.4.0 of Clafer Tools for Windows, Mac, and Linux,
can be downloaded from
[Clafer Tools - Binary Distributions](http://gsd.uwaterloo.ca/clafer-tools-binary-distributions).

1. download the binaries and unpack `<target directory>` of your choice
2. add the `<target directory>` to your system path so that the executables can be found

### Installation from Hackage

Dependencies

* [The Haskell Platform](http://hackage.haskell.org/platform/) v2014.2.0.0
  * Alternatively GHC >= 7.8.3 and Cabal >= 1.18

Clafer is now available on [Hackage](http://hackage.haskell.org/package/clafer-0.4.0/) and it can be installed using

1. `cabal update`
2. `cabal install clafer`
3. `cd <cabal's lib or share folder>`  (`C:\Users\<user>\AppData\Roaming\cabal\x86_64-windows-ghc-7.8.3\clafer-0.4.0` on Windows or `.cabal/share/x86_64-linux-ghc-7.8.3/clafer-0.4.0/` on Linux)
4. to automatically download Alloy jars
  * execute `make` in `tools`

### Installation from the source code

Dependencies

* [The Haskell Platform](http://hackage.haskell.org/platform/) v2014.2.0.0
  * Alternatively GHC >= 7.8.3 and Cabal >= 1.18
* [Alloy4.1 and/or Alloy4.2](http://alloy.mit.edu/alloy/download.html)
  * downloaded automatically during the build
* [Git](http://git-scm.com/)

On Windows

* [MSYS2](http://msys2.sourceforge.net/)
  * download MSYS2 installer
  * in MSYS2 console, execute
     * `pacman -Syu`
     * `pacman -S make wget unzip diffutils`

#### Important: Branches must correspond

All related projects are following the *simultaneous release model*.
The branch `master` contains releases, whereas the branch `develop` contains code under development.
When building the tools, the branches should match.
Releases from branches 'master` are guaranteed to work well together.
Development versions from branches `develop` should work well together but this might not always be the case.

#### Building

1. install the dependencies
2. open the command line terminal. On Windows, open MSYS2 terminal.
3. in some `<source directory>` of your choice, execute
  * `git clone git://github.com/gsdlab/clafer.git`
4. in `<source directory>/clafer`, execute
  * `cabal update`
  * `make init`
  * `make`

### Installation

1. Execute
  * `make install to=<target directory>`

#### Note:
> On Windows, use `/` with the `make` command instead of `\`.

## Integration with Sublime Text 2/3

See [ClaferToolsST](https://github.com/gsdlab/ClaferToolsST)

## Integration with VIM

See [clafer-vim](https://github.com/wasowski/clafer-vim)

Usage
=====

## Clafer Compiler

(As printed by `clafer --help`)

```
Clafer 0.4.0

clafer [OPTIONS] [FILE]

Common flags:
  -m --mode=CLAFERMODE                    Generated output type. Available
                                          CLAFERMODEs are: 'alloy' (Alloy 4.1);
                                          'alloy42' (default, Alloy 4.2); 'json'
                                          (intermediate representation of Clafer
                                          model); 'clafer' (analyzed and desugared
                                          clafer model); 'html' (original model
                                          in HTML); 'graph' (graphical
                                          representation written in DOT
                                          language); 'cvlgraph' (cvl notation
                                          representation written in DOT
                                          language); 'python' (generates IR in
                                          python); 'choco' (Choco constraint
                                          programming solver). Multiple modes
                                          can be specified at the same time,
                                          e.g., '-m alloy -m html'.
  -o --console-output                     Output code on console.
  -i --flatten-inheritance                Flatten inheritance ('alloy' and
                                          'alloy42' modes only).
     --timeout-analysis=INT               Timeout for analysis.
  -l --no-layout                          Don't resolve off-side rule layout.
     --nl --new-layout                    Use new fast layout resolver
                                          (experimental).
  -c --check-duplicates                   Check duplicated clafer names in
                                          the entire model.
  -f --skip-resolver                      Skip name resolution.
  -k --keep-unused                        Keep uninstantated abstract clafers
                                          ('alloy' and 'alloy42' modes only).
  -s --no-stats                           Don't print statistics.
  -v --validate                           Validate outputs of all modes. Uses
                                          'tools/alloy4.jar' and
                                          'tools/alloy4.2.jar' for Alloy
                                          models, and Clafer translator for
                                          desugared Clafer models. Use
                                          '--tooldir' to override the default
                                          location of these tools.
     --nr --noalloyruncommand             For usage with partial instances:
                                          Don't generate the alloy 'run show
                                          for ... ' command, and rename @.ref
                                          with unique names  ('alloy' and
                                          'alloy42' modes only).
     --tooldir=DIR                        Specify the tools directory
                                          ('validate' only). Default: 'tools/'.
  -a --alloy-mapping                      Generate mapping to Alloy source
                                          code ('alloy' and 'alloy42' modes
                                          only).
     --self-contained                     Generate a self-contained html
                                          document ('html' mode only).
     --add-graph                          Add a graph to the generated html
                                          model ('html' mode only). Requires
                                          the "dot" executable to be on the
                                          system path.
     --sr --show-references               Whether the links for references
                                          should be rendered. ('html' and
                                          'graph' modes only).
     --add-comments                       Include comments from the source
                                          file in the html output ('html' mode
                                          only).
  -e --ecore2clafer                       Translate an ECore model into
                                          Clafer.
     --ss=SCOPESTRATEGY --scope-strategy  Use scope computation strategy:
                                          none or simple (default).
     --check-afm --afm                    Throws an error if the cardinality
                                          of any of the clafers is above 1.
     --sg --skip-goals                    Skip generation of Alloy code for
                                          goals. Useful for all tools working
                                          with standard Alloy.
     --meta-data                          Generate a 'fully qualified
                                          name'-'least-partially-qualified
                                          name'-'unique ID' map ('.cfr-map').
                                          In Alloy, Alloy42, and Choco modes,
                                          generate the scopes map
                                          ('.cfr-scope').
  -? --help                               Display help message
  -V --version                            Print version information
     --numeric-version                    Print just the version number
```

The dependencies among the command line arguments are described on the [model wiki](http://t3-necsis.cs.uwaterloo.ca:8091/ClaferTools/CommandLineArguments).

Multiple modes can be used at the same time. For example,

`clafer model.cfr -m alloy -m json -m html -m graph --self-contained --show-references --no-stats`

The mode `-m alloy42` is only the default mode if no other modes are given. When other modes are given, the mode `-m alloy42` must be added explicitly if needed.

Additionally, `[OPTIONS]` can also be specified directly in the model file by inserting the following compiler directive as the first line of the file:

```
//# [OPTIONS]
```

for example

```
//# --keep-unused -m=alloy
```

Options given at command line override the options given in the file using `//#` which, in turn, override the defaults.

### Using compiler directives

Compiler directives are comments of the form

```
//# <directive name>
```

The following directives are markers of locations in the input files for different purposes:

* `//# FRAGMENT` - marks the beginning of the new [module fragment](http://gsd.uwaterloo.ca:8888/question/463/multi-fragment-modules).
* `//# GRAPH` - marks the insertion point for a graph rendering. The graph is only produced in HTML mode with the argument `--add-graph`.
* `//# STATS` - marks the insertion point for module statistics. The statistics can be omitted using the argument `--no-stats`.
* `//# SUMMARY` - shorthand for `//# GRAPH` and `//# STATS`
* `//# QUALITY_ATTRIBUTE` - is used by ClaferMooVisualizer and ClaferConfigurator to distinguish quality attributes, which should be filtered out, from other clafers.

# Need help?

* Visit [language's website](http://clafer.org).
* Report issues to [issue tracker](https://github.com/gsdlab/clafer/issues)
