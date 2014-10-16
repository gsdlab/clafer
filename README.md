Clafer
======

v0.3.7

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

Clafer Compiler
===============

Clafer compiler provides a reference language implementation. 
It translates models in Clafer to other formats (e.g., Alloy, XML, Python, JS, HTML, DOT) to allow for reasoning and processing with existing tools (Alloy Analyzer, Choco3, and Z3 SMT solver).

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

Contributors
------------

* [Kacper Bak](http://gsd.uwaterloo.ca/kbak), Original developer.
* [Jimmy Liang](http://gsd.uwaterloo.ca/jliang), Main developer.
* [Michał Antkiewicz](http://gsd.uwaterloo.ca/mantkiew), Requirements, development, architecture, testing, technology transfer.
* [Ed Zulkoski](http://gsd.uwaterloo.ca/ezulkosk), Python IR Generator.
* Luke Michael Brown, co-op student May-Aug 2013. Many improvements.
* [Rafael Olaechea](http://gsd.uwaterloo.ca/rolaechea), Multi-Objective Optimization extensions.

Getting the Clafer Compiler
---------------------------

Clafer can be installed from a binary distribution (preferred), from Hackage, and from the source code.

### Dependencies for running

Regardless of the installation method, the following are 

Required:

* [GNU Linear Programming Kit](http://www.gnu.org/software/glpk/) v4.55
  * On Windows, [WinGLPK](http://winglpk.sourceforge.net/)

Optional:

* [Java Platform (JDK)](http://www.oracle.com/technetwork/java/javase/downloads/index.html) v7+, 32bit
  * needed only for running XML output validation
* [Alloy4.1 and/or Alloy4.2](http://alloy.mit.edu/alloy/download.html)
  * needed only for Alloy output validation
* [GraphViz](http://graphviz.org/)
  * the program `dot` is needed only in the `html` mode for SVG graph generation

### Installation of GLPK

On Linux

1. [libglpk-dev](http://www.gnu.org/software/glpk/) v4.55
  * execute `sudo apt-get install libglpk-dev` on Ubuntu
2. [libgmp-dev](http://gmplib.org/)
  * execute `sudo apt-get install libgmp-dev` on Ubuntu

On Windows

1. The binary distribution already includes the GNU Linear Programming Kit DLL `glpk_4_55.dll`.
2. Install [WinGLPK](http://winglpk.sourceforge.net/) v4.55
  * inside the `w64` folder, copy `glpk_4_55.dll` to `glpk.dll` so that it can be found when building Haskell package `glpk-hs`
  * from `w64` folder, copy `glpk_4_55.dll` to `<user>\AppData\Roaming\cabal\bin`

On Mac

1. install GPLK 4.55 from [MacPorts](http://www.macports.org/)
  * execute `sudo port install glpk +universal`

### Installation from binaries

Binary distributions of the release 0.3.7 of Clafer Tools for Windows, Mac, and Linux, 
can be downloaded from 
[Clafer Tools - Binary Distributions](http://http://gsd.uwaterloo.ca/clafer-tools-binary-distributions). 

1. download the binaries and unpack `<target directory>` of your choice
2. add the `<target directory>` to your system path so that the executables can be found

### Installation from Hackage

Dependencies

* [The Haskell Platform](http://hackage.haskell.org/platform/) v2014.2.0.0 64bit
  * on Windows, use 32bit

Clafer is now available on [Hackage](http://hackage.haskell.org/package/clafer-0.3.7/) and it can be installed using

1. `cabal update`
2. `cabal install clafer`
3. `cd <cabal's lib or share folder>`  (`C:\Users\<user>\AppData\Roaming\cabal\x86_64-windows-ghc-7.8.3\clafer-0.3.7` on Windows or `.cabal/share/x86_64-linux-ghc-7.8.3/clafer-0.3.7/` on Linux)
4. to automatically download Alloy jars
  * execute `make` in `tools` 

On Windows 

* copy GLPK's dll `glpk_4_55.dll` to the `C:\Users\<user>\AppData\Roaming\cabal\bin` folder or any other folder on the system `PATH`

### Installation from the source code

Dependencies

* [The Haskell Platform](http://hackage.haskell.org/platform/) v2014.2.0.0 64bit
  * on Windows, use 32bit
  * Cabal >= 1.18
* [Alloy4.1 and/or Alloy4.2](http://alloy.mit.edu/alloy/download.html)
  * downloaded automatically during the build
* [Git](http://git-scm.com/)

On Windows 

* [MSYS2](http://msys2.sourceforge.net/) 
  * download MSYS2 installer
  * in MSYS2 console, execute `pacman -S make wget unzip`

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
5. On Linux and Mac execute 
  * `make init`
  * `make`
6. On Windows (in MSYS2 console), execute 
  * `make glpk=/c/<your WinGLPK install dir>`

### Installation

1. On Linux and Mac execute 
  * `make install to=<target directory>` 
2. On Windows (in MSYS2 console), execute 
  * `make glpk=/c/<your WinGLPK instal dir> to=/c/Users/<your user name>/AppData/Roaming/cabal/bin`

#### Note: 
> On Windows, use `/` with the `make` command instead of `\`.

Integration with Sublime Text 3
-------------------------------

See [clafer-tools-st3](https://github.com/gsdlab/clafer-tools-st3)


Usage
=====

Clafer Compiler
---------------

(As printed by `clafer --help`)

```
Clafer 0.3.7

clafer [OPTIONS] [FILE]

Common flags:
  -m --mode=CLAFERMODE                    Generated output type. Available
                                          CLAFERMODEs are: 'alloy' (Alloy 4.1);
                                          'alloy42' (default, Alloy 4.2);
                                          'xml' (intermediate representation of
                                          Clafer model); 'clafer' (analyzed and
                                          desugared clafer model); 'html'
                                          (original model in HTML); 'graph'
                                          (graphical representation written in
                                          DOT language); 'cvlgraph' (cvl
                                          notation representation written in
                                          DOT language); 'python' (generates IR
                                          in python); 'choco' (Choco constraint
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
     --schema                             Show Clafer IR (intermediate
                                          representation) XML schema.
  -v --validate                           Validate outputs of all modes. Uses
                                          'tools/XsdCheck.class' for XML,
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
                                          none, simple (default), or full.
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
```

The dependencies among the command line arguments are described on the [model wiki](http://t3-necsis.cs.uwaterloo.ca:8091/ClaferTools/CommandLineArguments).

Multiple modes can be used at the same time. For example, 

`clafer model.cfr -m alloy -m xml -m html -m graph --self-contained --show-references --no-stats`

The mode `-m alloy42` is only a default mode if no other modes are given. When other modes are given, the mode `-m alloy42` must be added explicitly if needed.

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

Need help?
==========
* See [language's website](http://clafer.org) for news, technical reports and more
  * Check out a [Learning Clafer section](http://t3-necsis.cs.uwaterloo.ca:8091/#Learning Clafer)
  * Try a live instance of [ClaferWiki](http://t3-necsis.cs.uwaterloo.ca:8091) which contains a repository of models for various applications
  * Try a live instance of [ClaferIDE](http://t3-necsis.cs.uwaterloo.ca:8094)
  * Try a live instance of [ClaferConfigurator](http://t3-necsis.cs.uwaterloo.ca:8093)
  * Try a live instance of [ClaferMooVisualizer](http://t3-necsis.cs.uwaterloo.ca:8092)
* Take a look at (incomplete) [Clafer by examples wiki](https://github.com/gsdlab/clafer/wiki)
* Browse example models in the [test suite](https://github.com/gsdlab/clafer/tree/master/test/positive) and [MOO examples](https://github.com/gsdlab/clafer/tree/master/spl_configurator/dataset)
* Post questions, report bugs, suggest improvements [GSD Lab Bug Tracker](http://gsd.uwaterloo.ca:8888/questions/). Tag your entries with `clafer` (so that we know what they are related to) and with `jimmy-liang` or `michal` (so that Jimmy or Michał gets a notification).