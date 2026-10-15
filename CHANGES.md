##### Clafer Version 0.5.3, unreleased

Minor release: compiler fixes found with larger example models, the integer range of the Choco output, and a reorganized test suite.

* Type checker: no crash on arithmetic over `max`/`min` of a union, or on if/then/else over unions and dereferenced references.
* Alloy output: `a - b` was generated as `-a`; `parent` of a top-level abstract clafer is the union of the parent relations of its subclafers ([#84](https://github.com/gsdlab/clafer/issues/84)).
* References: `-> 1` lost the constant ([#89](https://github.com/gsdlab/clafer/issues/89)); redefinition of an inherited abstract clafer ([#86](https://github.com/gsdlab/clafer/issues/86)); Choco references to set expressions were dropped; unused abstract clafers named by a reference or a constraint are kept.
* Implicit `.dref` in unions (`BobPicks ++ 3`, `others ++ p1`); `sum` and `product` over a union.
* Inside a reference clafer, an ancestor (`Machine`, `parent`) is the enclosing instance, and the children of the target resolve through the reference.
* Scope inference covers the lower bound of group cardinalities.
* Sibling clafers on one line (`b : B A 3`) are a parse error.
* New options `--minint` and `--maxint` (also in `//# OPTIONS`) set the integer range of the Choco output.
* The example models and regression tests run in the `model-tests` suite (flag `model-tests`, off by default) and are not part of the package.
* [Release](https://github.com/gsdlab/clafer/pull/99)

##### Clafer Version 0.5.2 released on Oct 9, 2026

Minor release, Haskell compatibility (GHC 9.6.7 and lts-22.44).

* [Release](https://github.com/gsdlab/clafer/pull/98)

##### Clafer Version 0.5.1 released on Sep 12, 2023

Minor release, latest Haskell compatibility (GHC 9.4.6 and LTS-21.11).

* [Release](https://github.com/gsdlab/clafer/pull/95)

##### Clafer Version 0.5.0 released on Jan 31, 2018

This major release adds behavioral modeling capability to Clafer.

* [Release](https://github.com/gsdlab/clafer/pull/94)

##### Clafer Version 0.4.5 released on Mar 13, 2017

* [Release](https://github.com/gsdlab/clafer/pull/91)

##### Clafer Version 0.4.4 released on Jun 23, 2016

* [Release](https://github.com/gsdlab/clafer/pull/88)

##### Clafer Version 0.4.3 released on Dec 22, 2015

* [Release](https://github.com/gsdlab/clafer/pull/81)

##### Clafer Version 0.4.2.1 released on Oct 19, 2015

* Fixed Haddock build, updated README, fixed a test case.

##### Clafer Version 0.4.2 released on Oct 16, 2015

* [Release](https://github.com/gsdlab/clafer/pull/74)

##### Clafer Version 0.4.1 released on Sep 1, 2015

* [Release](https://github.com/gsdlab/clafer/pull/71)

##### Clafer Version 0.4.0 released on Jul 28, 2015

* [Release](https://github.com/gsdlab/clafer/pull/68)

##### Clafer Version 0.3.10 released on April 24, 2015

* [Release](https://github.com/gsdlab/clafer/pull/66)

##### Clafer Version 0.3.9 released on March 06, 2015

* [Release](https://github.com/gsdlab/clafer/pull/63)

##### Clafer Version 0.3.8 released on January 27, 2015

* [Release](https://github.com/gsdlab/clafer/pull/60)

##### Clafer Version 0.3.7 released on October 23, 2014

* [Release](https://github.com/gsdlab/clafer/pull/53)

##### Clafer Version 0.3.6.1 released on July 08, 2014

* [Release](https://github.com/gsdlab/clafer/pull/50)

##### Clafer Version 0.3.6 released on May 23, 2014

* [Release](https://github.com/gsdlab/clafer/pull/48)

##### Clafer Version 0.3.5 released on January 20, 2014

* [Release](https://github.com/gsdlab/clafer/pull/44)

##### Clafer Version 0.3.4 released on September 20, 2013

##### Clafer Version 0.3.3 released on August 14, 2013

* [Release](https://github.com/gsdlab/clafer/pull/35)

##### Clafer Version 0.3.2 released on April 11, 2013

##### Clafer Version 0.3.1 released on October 17, 2012

##### Clafer Version 0.3 released on July 17, 2012

This was the first release of Clafer and included all code since the beginning of the project.

Basic features - See the `README.md`.
