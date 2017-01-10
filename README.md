[![Hackage](https://img.shields.io/hackage/v/clafer.svg)](https://hackage.haskell.org/package/clafer)
[![Build Status](https://secure.travis-ci.org/gsdlab/clafer.svg)](http://travis-ci.org/gsdlab/clafer)

# Clafer, the language

##### v0.4.4


[Clafer](http://clafer.org) is a general-purpose lightweight structural modeling language developed by
[GSD Lab](http://gsd.uwaterloo.ca/), [University of Waterloo](http://uwaterloo.ca), and
[MODELS](http://www.itu.dk/research/models/) group at [IT University of Copenhagen](http://www.itu.dk/).
Clafer can be used for modeling of static hierarchical structures and for modeling the change of the structures over time (behavior). Clafer allows for naturally expressing variability in both the structure and behavior.
The main goal of Clafer is to make modeling more accessible to a wider range of users and domains.

There are many possible applications of Clafer; however, three are prominent:

1. *Product-Line Architecture Modeling* - aims at representing and managing commonality and variability of assets in product lines and creating and verifying product configurations.
Clafer naturally supports multi-staged configuration.
By applying modeling patterns, Clafer can be used for feature modeling, architecture modeling (e.g., by applying EAST-ADL), and behavior modeling (e.g., hierarchical state transition systems). All these aspects naturally include variability.

2. *Multi-Objective Product Optimization* - aims at finding a set of products in a given product line that are optimal with respect to a set of objectives.
Clafer multi-objective optimizer generates a Pareto front of optimal product configurations.

3. *Domain Modeling* - aims at improving the understanding of the problem domain in the early stages of software development and determining the requirements with fewer defects.
This is also known as *Concept Modeling* or *Ontology Modeling*.

May applications actually combine the three. For example, see [Technical Report: Case Studies on E/E Architectures for Power Window and Central Door Locks Systems](http://www.clafer.org/2016/06/technical-report-case-studies-on-ee.html).

### Resources

* [Learning Clafer](http://t3-necsis.cs.uwaterloo.ca:8091/#learning-clafer)
* [Cheat Sheet](doc/CheatSheet.md)
* [Syntax Documentation](doc/clafer.pdf)
* [Grammar](src/clafer.cf)

# Clafer, the compiler

Clafer compiler provides a reference implementation of Clafer, the language.
It translates models in Clafer to other formats (e.g., Alloy, JSON, JS, HTML, DOT) to allow for reasoning and processing with existing tools (Alloy Analyzer, Choco3, and GraphViz).

Currently, the compiler is used by

* Backends
  * Alloy-based Instance Generator ([ClaferIG](https://github.com/gsdlab/claferIG)),
  * Choco3-based Instance Generator and Multi-Objective Optimizer ([chocosolver](https://github.com/gsdlab/chocosolver).
* Web Frontends
  * Clafer Integrated Development Environment ([ClaferIDE](https://github.com/gsdlab/claferIDE)),
  * Clafer Configurator ([ClaferConfigurator](https://github.com/gsdlab/ClaferConfigurator)),
  * Multi-Objective [Visualizer and Explorer](https://github.com/gsdlab/ClaferMooVisualizer), and
  * Clafer Wiki ([ClaferWiki](https://github.com/gsdlab/claferwiki)).

## Contributors

* [Michał Antkiewicz](http://gsd.uwaterloo.ca/mantkiew), Main developer.
* [Kacper Bak](http://gsd.uwaterloo.ca/kbak), Original developer.
* [Jimmy Liang](http://gsd.uwaterloo.ca/jliang), Developer.
* Luke Michael Brown, co-op student May-Aug 2013. Many improvements.
* Paulius Juodisius, [customized BNFC generator](https://github.com/juodaspaulius/bnfc) and layout resolver.
* [Rafael Olaechea](http://gsd.uwaterloo.ca/rolaechea), Multi-Objective Optimization extensions.

## Getting the Clafer compiler

Clafer can be installed from a binary distribution (preferred), from Hackage, and from the source code.

### Dependencies for running

Regardless of the installation method, the following are

Optional:

* [Java Platform (JDK)](http://www.oracle.com/technetwork/java/javase/downloads/index.html) v8+, 64bit
  * only needed for running Alloy validation
  * 32bit on Windows
* [Alloy4.2](http://alloy.mit.edu/alloy/download.html)
  * only needed for Alloy output validation
* [GraphViz](http://graphviz.org/)
  * the program `dot` is needed only in the `html` mode for SVG graph generation

### Installation from binaries

Binary distributions of the release 0.4.4 of Clafer Tools for Windows, Mac, and Linux,
can be downloaded from
[Clafer Tools - Binary Distributions](http://gsd.uwaterloo.ca/clafer-tools-binary-distributions).

1. Download the binaries and unpack `<target directory>` of your choice.
2. Add the `<target directory>` to your system path so that the executables can be found.

### Installation from Hackage

Clafer is available on [Hackage](http://hackage.haskell.org/package/clafer-0.4.4/) and it can be installed using either [`stack`](https://github.com/commercialhaskell/stack) or [`cabal-install`](https://hackage.haskell.org/package/cabal-install).

#### Installation using `stack`

Stack is the only requirement: no other Haskell tooling needs to be installed because stack will automatically install everything that's needed.

1. [Install `stack`](https://github.com/commercialhaskell/stack#how-to-install)
   * (first time only) Execute `stack setup`.
2. Execute `stack install clafer`.

#### Installation using `cabal-install`

Dependencies

* [GHC](https://www.haskell.org/downloads) >= 7.10.3 or 8.0.1 are recommended,
* `cabal-install` >= 1.22, should be installed together with a GHC distribution,
* [alex](https://hackage.haskell.org/package/alex),
* [happy](https://hackage.haskell.org/package/happy).

1. Install GHC
2. `cabal update`
3. `cabal install alex happy`
4. `cabal install clafer`
5. on Windows `cd C:\Users\<user>\AppData\Roaming\cabal\x86_64-windows-ghc-8.0.1\clafer-0.4.4`
6. on Linux `ca ~/.cabal/share/x86_64-linux-ghc-8.0.1/clafer-0.4.4/`
7. to automatically download Alloy jars, execute
  * `make alloy4.2.jar`,
  * move `alloy4.2.jar` to the location of the clafer executable.

### Installation from the source code

Dependencies

* [`stack`](https://github.com/commercialhaskell/stack#how-to-install)
* [Git](http://git-scm.com/)

On Windows

* [MSYS2](http://msys2.sourceforge.net/)
  * it is installed automatically by `stack setup`
  * update MSYS2 following the [update procedure](http://sourceforge.net/p/msys2/wiki/MSYS2%20installation/):
    * `stack exec pacman -- -Sy`
    * `stack exec pacman -- --needed -S bash pacman pacman-mirrors msys2-runtime`
    * restart shell if the runtime was updated
    * `stack exec pacman -- -Su`
  * `stack exec pacman -- -S make wget unzip diffutils`

#### Important: branches must correspond

All related projects are following the *simultaneous release model*.
The branch `master` contains releases, whereas the branch `develop` contains code under development.
When building the tools, the branches should match.
Releases from branches 'master` are guaranteed to work well together.
Development versions from branches `develop` should work well together but this might not always be the case.

#### Building

1. in some `<source directory>` of your choice, execute
  * `git clone git://github.com/gsdlab/clafer.git`
2. in `<source directory>/clafer`, execute `stack setup`. This will install all dependencies, build tools, and MSYS2 (on Windows).
3. `cd <source directory>`
  * `make` on Linux/Mac
  * `stack exec make` on Windows

### Installation

1. Execute
  * `make install to=<target directory>` on Linux/Mac
  * `stack exec make install to=<target directory>` on Windows

#### Note:
> On Windows, use `/` with the `make` command instead of `\`, e.g., `make install to=/c/clafer-tools-0.4.4/`

## Integration with Sublime Text 2/3

See [ClaferToolsST](https://github.com/gsdlab/ClaferToolsST)

## Integration with VIM

See [clafer-vim](https://github.com/wasowski/clafer-vim)

## Usage

### Clafer Compiler

(As printed by `clafer --help`)

```
Clafer 0.4.4

clafer [OPTIONS] [FILE]

Common flags:
  -m --mode=CLAFERMODE                    Generated output type. Available
                                          CLAFERMODEs are: 'alloy' (default,
                                          Alloy 4.2); 'json' (intermediate
                                          representation of Clafer model);
                                          'clafer' (analyzed and desugared
                                          clafer model); 'html' (original model
                                          in HTML); 'graph' (graphical
                                          representation written in DOT
                                          language); 'cvlgraph' (cvl notation
                                          representation written in DOT
                                          language); 'choco' (Choco constraint
                                          programming solver). Multiple modes
                                          can be specified at the same time,
                                          e.g., '-m alloy -m html'.
  -o --console-output                     Output code on console.
  -i --flatten-inheritance                Flatten inheritance ('alloy' mode
                                          only).
     --timeout-analysis=INT               Timeout for analysis.
  -l --no-layout                          Don't resolve off-side rule layout.
  -n --nl --new-layout                    Use new fast layout resolver
                                          (experimental).
  -c --check-duplicates                   Check duplicated clafer names in
                                          the entire model.
  -f --skip-resolver                      Skip name resolution.
  -k --keep-unused                        Keep uninstantated abstract clafers
                                          ('alloy' mode only).
  -s --no-stats                           Don't print statistics.
  -v --validate                           Validate outputs of all modes. Uses
                                          '<tooldir>/alloy4.2.jar' for Alloy
                                          models, '<tooldir>/chocosolver.jar'
                                          for Alloy models, and Clafer
                                          translator for desugared Clafer
                                          models. Use '--tooldir' to override
                                          the default location ('.') of these
                                          tools.
     --tooldir=DIR                        Specify the tools directory
                                          ('validate' only). Default: '.'
                                          (current directory).
  -a --alloy-mapping                      Generate mapping to Alloy source
                                          code ('alloy' mode only).
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
     --meta-data                          Generate a 'fully qualified
                                          name'-'least-partially-qualified
                                          name'-'unique ID' map ('.cfr-map').
                                          In Alloy and Choco modes, generate
                                          the scopes map ('.cfr-scope').
  -? --help                               Display help message
  -V --version                            Print version information
     --numeric-version                    Print just the version number
```

The dependencies among the command line arguments are described on the [model wiki](http://t3-necsis.cs.uwaterloo.ca:8091/ClaferTools/CommandLineArguments).

Multiple modes can be used at the same time. For example,

`clafer model.cfr -m alloy -m json -m html -m graph --self-contained --show-references --no-stats`

The mode `-m alloy` is only the default mode if no other modes are given. When other modes are given, the mode `-m alloy` must be added explicitly if needed.

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

# Developing Clafer

Here is some information about the development of the Clafer compiler.

## Branching

We are following the simplified version of the [successful Git branching model](http://nvie.com/posts/a-successful-git-branching-model/).
The branch `master` is for releases and hot fixes only.
The branch `develop` is for minor development and for integration of features from feature branches.
For any substantial work, branch off from `develop` and create a pull request back into `develop` after the work is completed.
We do testing and code review before merging into develop.
If the `develop` is ahead, merge it into the feature branch and perform integration testing there.
To make a release, we create a pull request from `develop` into `master`.
We tag `master` with version numbers after each release merge.

## Building

We have switched to [Haskell Tool Stack](https://github.com/commercialhaskell/stack#the-haskell-tool-stack).
Install the tool first.

## Testing

We have both automated tests and regression tests.

To run the automated tests (including both unit tests and [doctests](https://github.com/sol/doctest#readme)), execute

```
stack test
```

To only run unit tests, execute `stack test test-suite`.

To only run doctests, execute `stack test doctests`.

> Note: it is still possible to run `cabal test` as previously; however, the `Makefile` uses `stack` by default.

For instructions for adding new modules to the doctest suite, see [cabal integration](https://github.com/sol/doctest#cabal-integration).

To run all the automated tests and the regression tests, execute

```
make test
```

We do test-driven development in the following way:

1. create a test case Clafer model in either `test/positive` or `test/negative` depending on whether a test case should compile successfully or return an error. For example, see a positive test case [test/positive/redefinition.cfr](https://github.com/gsdlab/clafer/blob/namedDrefs/test/positive/redefinition.cfr).
2. produce the intended compiler output automatically if possible and manually fix the output. Save the intended output as a regression test case. For example, see [test/regression/redefinition.cfr.reg](https://github.com/gsdlab/clafer/blob/namedDrefs/test/regression/redefinition.als.reg).
3. implement the feature to reproduce the intended output: compiler the test case and execute

```
cd test
make diffRegressions
```

this will show you how the current output diverges from the intended output.


## Modifying the grammar

We are using a [customized version of BNCF](https://github.com/juodaspaulius/bnfc).
Clone the repository and install a binary of `bnfc` so that it's visible in your `PATH`.
After changing the grammar, execute

```
make grammar
```


# Need help?

* Visit [language's website](http://clafer.org).
* Report issues to [issue tracker](https://github.com/gsdlab/clafer/issues)
