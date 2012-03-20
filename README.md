Clafer
======

[Clafer](http://clafer.org) is a general purpose lightweight modeling language developed at [GSD Lab](http://gsd.uwaterloo.ca/), [University of Waterloo](http://uwaterloo.ca). Lightweight modeling aims at improving the understanding of the problem domain in the early stages of software development and determining the requirements with fewer defects. Clafer's goal is to make modeling more accessible to a wider range of users and domains. 

Clafer Translator
=================

Clafer translator provides a reference language implementation. It translates models in Clafer to other formats (e.g. Alloy, XML) to allow for reasoning with existing tools.


Currently, the translator is used by Clafer Instance Generator ([ClaferIG](https://github.com/gsdlab/claferIG)).

Dependencies
------------
* GHC (Glasgow Haskell Compiler). For installation instructions refer to the [GHC website](http://www.haskell.org/ghc/distribution_packages)
* [cabal-install](http://www.haskell.org/haskellwiki/Cabal-Install) (for installation and fetching required Haskell libraries). The package can be installed as follows (Ubuntu):
```
sudo apt-get install cabal-install
```

alternatively, you may install [The Haskell Platform](http://hackage.haskell.org/platform/). It includes both GHC and cabal-install.

### Extra Dependencies

* [Alloy4.1 or 4.2](http://alloy.mit.edu/) (backend reasoner)


### Prerequisites

1. install [Git](http://git-scm.com/)
2. install the Haskell Platform (it contains GHC and Cabal)
3. create a `<target directory>` of your choice
4. make sure the `<target directory>` is on your command PATH
5. in another directory, `<source directory>`, execute `git clone git://github.com/gsdlab/clafer.git`

### Building

1. in the newly created `<source directory>/clafer` directory, execute
  * `cabal update`
  * `cabal install`

#### Note: 
> On Windows, install Cygwin with the `make` package.

### Installation

1. execute `make deploy to=<target directory>`

#### Note: 
> On Windows, use `/` with the `make` command instead of `\`.

Usage
-----

### Command-line Usage

`clafer <model file name>.cfr`

- by default, the translator produces Alloy 4 output. Use

  * `-m=xml` 	to produce XML output
  * `-m=clafer` 	to produce desugared Clafer output
  * `-m=alloy42` 	to produce Alloy 4.2 output
  * `-m=alloy` 	to produce Alloy 4.1 output (default)

Validator
=========

The clafer translator can validate its XML, Alloy 4 and 4.2, and Clafer output.

Dependencies
------------
* Java >= 5
* XsdCheck.class (for validating XML output against Clafer XSD schema)
* Alloy binaries (alloy4.jar and/or alloy4.2-rc.jar) are placed in `<target directory>/tools`.

Usage
-----

* `-v` 		to invoke the validator for the given kind of output

Need help?
==========
* See [Project's website](http://gsd.uwaterloo.ca/clafer) for news, technical reports and more
  * Check out a [Clafer tutorial](http://gsd.uwaterloo.ca/node/310)
  * Try [Online translator](http://gsd.uwaterloo.ca/clafer/translator)
* Take a look at incomplete [Clafer wiki](https://github.com/gsdlab/clafer/wiki)
* Browse example models in the [test suite](https://github.com/gsdlab/clafer/tree/master/test/positive) 
* Post questions, report bugs, suggest improvements [GSD Lab Bug Tracker](http://gsd.uwaterloo.ca:8888/questions/). Tag your entries with `clafer` (so that we know what they are related to) and with `kacper-bak` or `jimmy-liang` (so that Kacper or Jimmy gets a notification).