Clafer
======

[Clafer](http://clafer.org) is a general-purpose lightweight structural modeling language developed at [GSD Lab](http://gsd.uwaterloo.ca/), [University of Waterloo](http://uwaterloo.ca). Clafer can be used for modeling of static structures but has no support for modeling the change of the structures over time (behavior). The main goal of Clafer is to make modeling more accessible to a wider range of users and domains. 

There are many possible applications of Clafer; however, three are prominent:

1. *Domain Modeling* - aims at improving the understanding of the problem domain in the early stages of software development and determining the requirements with fewer defects. This is also known as *Concept Modeling* or *Ontology Modeling*.

2. *Product-Line Modeling* - aims at representing and managing commonality and variability of assets in product lines and creating and verifying product configurations. Clafer naturally supports multi-staged configuration. 

3. *Multi-Objective Product Optimization* - aims at finding a set of products in a given product line that are optimal with respect to a set of objectives. Clafer multi-objective optimizer generates a Pareto front of optimal product configurations.

Clafer Compiler
===============

v0.3.12-9-2012

Clafer compiler provides a reference language implementation. It translates models in Clafer to other formats (e.g. Alloy, XML, HTML, DOT) to allow for reasoning and processing with existing tools.

Currently, the compiler is used by Clafer Instance Generator ([ClaferIG](https://github.com/gsdlab/claferIG)), Clafer Multi-Objective Optimizer (ClaferMOO), and Clafer Wiki ([ClaferWiki](https://github.com/gsdlab/claferwiki)).

Getting Clafer Tools
--------------------

Binary distributions of Clafer, ClaferMOO, and ClaferIG for Windows, Mac, and Linux, can be downloaded from [ClaferIG Downloads Page](https://github.com/gsdlab/claferig/downloads). ClaferMOO is a set of scripts in Python (cross-platform).
In case these binaries do not work on your particular machine configuration, the tools can be easily built from source code, as described below.

### Dependencies for running

* [Java Platform (JDK)](http://www.oracle.com/technetwork/java/javase/downloads/index.html) v6+, 32bit
* [Python](http://www.python.org/download/) v2.7.*
  * Needed only by ClaferMOO
* [Alloy4.1 and/or Alloy4.2](http://alloy.mit.edu/alloy/download.html)
* [Alloy4MOO](http://www.stevenstewart.ca/alloy4/alloy4moo.jar)
  * NOTE: Alloy4MOO is a pre-release experimental software. Use at own risk.
  * Needed only by ClaferMOO
* [GraphViz](http://graphviz.org/)
  * `dot` is needed only in the `html` mode for SVG graph generation

On Windows only

* [Cygwin](http://www.cygwin.com/)
  * Needed only by ClaferMOO
  
### Installation

1. download the binaries and unpack `<target directory>` of your choice
2. add the `<target directory>` to your system path so that the executables can be found
3. copy alloy's jars to the `<target directory>/tools` folder

Building & Installation From Source Code
----------------------------------------

### Additional dependencies for building

* Dependencies for running
* [The Haskell Platform](http://hackage.haskell.org/platform/) v.2012.2.0.0
* [Alloy4.1 and/or Alloy4.2](http://alloy.mit.edu/alloy/download.html)
  * downloaded automatically during build
* [Alloy4MOO](http://www.stevenstewart.ca/alloy4/alloy4moo.jar)
  * downloaded automatically during build
  * NOTE: Alloy4MOO is a pre-release experimental software. Use at own risk.
* [Git](http://git-scm.com/)

On Windows only

* [Cygwin](http://www.cygwin.com/) with packages `make`, `wget`, `unzip`

### Important: Branches must correspond

Clafer and ClaferIG are following the *simultaneous release model*. 
The branch `master` contains releases, whereas the branch `develop` contains code under development. 
When building the tools, the branches should match:
Releases `clafer/master` and `claferIG/master` are guaranteed to work well together.
Development versions `clafer/develop` and `claferIG/develop` should work well together but this might not always be the case.

### Building

1. install the dependencies
2. in some `<source directory>` of your choice, execute `git clone git://github.com/gsdlab/clafer.git`
3. in `<source directory>/clafer`, execute
  * `cabal update`
  * `make`

### Installation

1. execute `make install to=<target directory>`
2. add the `<target directory>` is on your command PATH

#### Note: 
> On Windows, use `/` with the `make` command instead of `\`.

Usage
=====

Clafer Compiler
---------------

(As printed by `clafer --help`)

```
Clafer v0.3.12-9-2012

clafer [OPTIONS] [FILE]

Common flags:
  -m --mode=CLAFERMODE         Generated output type. Available CLAFERMODEs are:
                               'alloy' (default, Alloy 4.1); 'alloy42' (Alloy
                               4.2); 'xml' (intermediate representation of
                               Clafer model); 'clafer'  (analyzed and desugared
                               clafer model); 'html' (original model in HTML);
                               'graph' (graphical representation written in DOT
                               language)
  -o --console-output          Output code on console
  -i --flatten-inheritance     Flatten inheritance (`alloy` and `alloy42` modes 
                               only)
     --timeout-analysis=INT    Timeout for analysis
  -l --no-layout               Don't resolve off-side rule layout
  -n --nl --new-layout         Use new fast layout resolver (experimental)
  -c --check-duplicates        Check duplicated clafer names
  -f --skip-resolver           Skip name resolution
  -k --keep-unused             Keep uninstantated abstract clafers (`alloy` and 
                               `alloy42` modes only)
  -s --no-stats                Don't print statistics
     --schema                  Show Clafer IR (intermediate representation) XML
                               schema
  -v --validate                Validate output. Uses 'tools/XsdCheck.class' for
                               XML,  'tools/alloy4.jar' and
                               'tools/alloy4.2.jar' for Alloy models, and
                               Clafer translator for desugared Clafer models. Use
                               --tooldir to override the default location of
                               these tools.
     --nr --noalloyruncommand  For usage with partial instances: Don't
                               generate the alloy 'run show for ... ' command,
                               and rename @.ref with unique names.
     --tooldir=DIR             Specify the tools directory. Default: 'tools/' 
                               (`validate` only)
  -a --alloy-mapping           Generate mapping to Alloy source code (`alloy` 
                               and `alloy42` modes only)
     --self-contained          Generate a self-contained html document. Only
                               works with html mode.
     --add-graph               Add a graph to the generated html model. Only
                               works with html mode and if the "dot" executable
                               is on the system path.
  -? --help                    Display help message
  -V --version                 Print version information
```

Additionally, `[OPTIONS]` can also be specified directly in the model file by inserting the following as the first line of the file:

```
//# [OPTIONS]
```

for example

```
//# --keep-unused -m=alloy42
```

Options given at command line override the options given in the file using `//#` which, in turn, override the defaults.

ClaferMoo
---------

`clafer_moo.sh [MODEL] [PATH TO CLAFER TOOLS]`

#### Note: 
> On Windows, run the script using Cygwin

Need help?
==========
* See [Project's website](http://gsd.uwaterloo.ca/clafer) for news, technical reports and more
  * Check out a [Clafer tutorial](http://gsd.uwaterloo.ca/node/310)
  * Try [Online translator](http://gsd.uwaterloo.ca/clafer/translator)
* Take a look at incomplete [Clafer wiki](https://github.com/gsdlab/clafer/wiki)
* Browse example models in the [test suite](https://github.com/gsdlab/clafer/tree/master/test/positive) and [MOO examples](https://github.com/gsdlab/clafer/tree/master/spl_configurator/dataset)
* Post questions, report bugs, suggest improvements [GSD Lab Bug Tracker](http://gsd.uwaterloo.ca:8888/questions/). Tag your entries with `clafer` (so that we know what they are related to) and with `kacper-bak` or `jimmy-liang` (so that Kacper or Jimmy gets a notification).