Clafer
======

Overview
--------
[Clafer](http://clafer.org) is a general purpose lightweight modeling language developed at [GSD Lab](http://gsd.uwaterloo.ca/), [University of Waterloo](http://uwaterloo.ca). Lightweight modeling aims at improving the understanding of the problem domain in the early stages of software development and determining the requirements with fewer defects. Clafer's goal is to make modeling more accessible to a wider range of users and domains. The tool provides a reference language implementation. It translates models to other formats (e.g. Alloy, XML) to allow for reasoning with existing tools.

Dependencies
------------
* GHC (Glasgow Haskell Compiler). For installation instructions refer to the [GHC website](http://www.haskell.org/ghc/distribution_packages)
* [cabal-install](http://www.haskell.org/haskellwiki/Cabal-Install) (for installation and fetching required Haskell libraries). The package can be installed as follows (Ubuntu):
```
sudo apt-get install cabal-install
```

alternatively, you may install [The Haskell Platform](http://hackage.haskell.org/platform/). It includes both GHC and cabal-install.

Extra Dependencies
------------------
* [Alloy] (http://alloy.mit.edu/) (backend reasoner)

Build
-----
```
  cabal update
  cabal install
```

Usage (Command-line)
--------------------
```
clafer <filename>.cfr
```
   
By default, the translator produces Alloy 4 output. Use

`-m=xml` 	to produce XML output

`-m=clafer` 	to produce desugared Clafer output

`-m=alloy42` 	to produce Alloy 4.2 output

`-m=alloy` 	to produce Alloy 4 output (default)

Validator
=========

The clafer translator can validate its XML, Alloy 4 and 4.2, and Clafer output.

Dependencies
------------
* Java >= 5
* XsdCheck.class (for validating XML output against Clafer XSD schema)
* Alloy binaries (alloy4.jar and/or alloy4.2-rc.jar) are placed in `<clafer installation folder>/tools` directory.

Usage (Command-line)
--------------------
`-v` 		to invoke the validator for the given kind of output
