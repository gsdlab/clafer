#!/bin/bash
# The oracle of check 8 (design/java-compiler-frontend-feasibility.md): the parse tree of each
# model as the compiler prints it (printTree), or its parse error with its position, for the
# Java frontend's parser to compare with (ClaferParserConformanceTest in chocosolver). The
# models are the sources of the positive suite, their rich and core explicit regressions, and
# the negative suite. Writes parse-trees/DIR/MODEL.tree; parse-trees is not committed.
#
# Usage, in clafer/test after cabal build: bash print-parse-trees.sh

set -e
cd "$(dirname "$0")"
rm -rf parse-trees
mkdir -p parse-trees/positive parse-trees/regression parse-trees/negative
run() {
  local dir=$1
  shift
  (cd .. && cabal exec -v0 -- runghc --ghc-arg=-package=clafer --ghc-arg=-package=filepath \
    test/print-parse-trees.hs "test/parse-trees/$dir" "$@")
}
run positive $(ls positive/*.cfr | grep -v -e '\.des\.cfr$' -e '\.core\.cfr$' | sed 's|^|test/|')
run regression $(ls regression/*.des.cfr.reg regression/*.core.cfr.reg | sed 's|^|test/|')
run negative $(ls negative/*.cfr | sed 's|^|test/|')
echo "$(find parse-trees -name '*.tree' | wc -l) parse trees in test/parse-trees"
