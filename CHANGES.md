##### Clafer Version 0.5.4, unreleased

* Models in several files: `--import=FILE`, in `//# OPTIONS` or on the command line, compiles the model together with the imported files, transitively, each file once and before the files importing it ([#100](https://github.com/gsdlab/clafer/issues/100)). The options of all files are combined. The model and its imports can be URLs; an import is relative to the importing file's folder or URL.
* Errors give their position as `file.cfr:line:column`, also in a model of one file (`Parse failed at model.cfr:3:5...`, previously `line 3 column 5`), and in a model with imports, the file in which they are. A model read from the standard input is `<stdin>`.
* A syntax error's message no longer repeats the line (`syntax error before ? }`), which in a model with imports was a line of the complete model; the position is given with the error.
* Models read from URLs: `https://` works (it was read as a local file name), outputs are named after the URL's last segment, in the current directory, and `ftp://` is no longer supported. The compiler uses http-client instead of the HTTP package.
* `//# OPTIONS`: an unknown option or a malformed directive is an error; the whole directive used to be ignored silently. When compiling with the `clafer` executable, a directive with `-m` or with an option's short or custom name (e.g., `-k`, `--check-afm`, `--nl`) was ignored entirely, and `--tl` and `--tooldir` in the directive were overridden by the defaults.
* Clafer names with apostrophes (`same'`) work with Alloy and Choco: an apostrophe is not allowed in their identifiers (in Alloy 6, it is the next-state operator), so it becomes `__prime__` in the clafer's UID (`c0_same__prime__`); the name keeps it. Such models are not counted as able to skip the name resolver.
* `opt` makes the children optional again, as in the language's definition: a child without a multiplicity is optional (`0..1`) under a keyword group (`xor`, `or`, `mux`, `opt`). Since 0.3.3, the default depended only on the interval, and `opt`, being `0..*` like no group at all, made its children mandatory. Only the keywords set `_isKeyword` in the IR, no longer the ranges `0..n`. Children of other ranges are optional and children of no group or `0..*` are mandatory, as before.
* A group cardinality whose lower bound the children cannot reach is a compile error, e.g., `xor` or `or` over no children, or `3..*` over two optional children. The children include the inherited ones, and the group cardinality may be inherited or redefined (`2..2 myGroup : SuperGroup`). Such groups were not constrained in the Alloy and Choco output. An abstract clafer's group is not checked, since its subclafers may add children.
* Layout: comments do not count in the indentation. A line which starts with a comment (`/*history*/ xor on`) is indented as if the comment was not there, at the column where the comment starts. The first clafer after the comment was nested by its own column, which put the following lines at wrong levels.
* JSON output: the IR has the source positions of the clafers (`_cinPos`) and expressions (`_inPos`), which were always `null`: `{"file": "model.cfr", "start": {"line": 2, "column": 3}, "end": {"line": 2, "column": 6}}`, the file and the position in it, with lines and columns from 1 and an exclusive end. A tab advances the column to the next multiple of 8, plus 1, as in the compiler's error messages. The span of a clafer with children ends one or two columns after its last token, at the closing brace that the layout resolver inserts. Desugared expressions without a position in the model are still `null`.
* HTML output: comments are escaped and shown as written (`--add-comments`); markup in a comment was rendered, and `--` in a `//#` comment could end the generated HTML comment early.
* HTML output: each file of the model starts with its name (`<div class="file">model.cfr</div>`), also a model of one file, and the comments before a `//# FRAGMENT` directive are shown before it. The HTML shown for a model with errors gives their positions as `file.cfr:line:column`, and an error message with quotes no longer ends the tooltip.

##### Clafer Version 0.5.3, Oct 15, 2026

Minor release: compiler fixes found with larger example models, the integer range of the Choco output, and a reorganized test suite.

* Type checker: no crash on arithmetic over `max`/`min` of a union, or on if/then/else over unions and dereferenced references.
* Alloy output: `a - b` was generated as `-a`; `parent` of a top-level abstract clafer is the union of the parent relations of its subclafers ([#84](https://github.com/gsdlab/clafer/issues/84)).
* References: `-> 1` lost the constant ([#89](https://github.com/gsdlab/clafer/issues/89)); redefinition of an inherited abstract clafer ([#86](https://github.com/gsdlab/clafer/issues/86)); Choco references to set expressions were dropped; unused abstract clafers named by a reference or a constraint are kept.
* Implicit `.dref` in unions (`BobPicks ++ 3`, `others ++ p1`); `sum` and `product` over a union.
* Inside a reference clafer, an ancestor (`Machine`, `parent`) is the enclosing instance, and the children of the target resolve through the reference.
* Scope inference covers the lower bound of group cardinalities.
* Sibling clafers on one line (`b : B A 3`) are a parse error.
* Alloy 6.2.0 (`alloy6.2.0.jar`, Java 17+) replaces Alloy 4.2; the generated Alloy models are unchanged. `--validate` runs all Alloy commands headlessly (`alloy exec`) and no longer opens the Alloy visualizer.
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
