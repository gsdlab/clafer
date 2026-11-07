#!/bin/bash
# Compares the outputs of the positive test suite (.als, .js, .des.cfr, .html, .dot) with their
# regressions, exactly, also their whitespace, and fails if any output differs, has no
# regression, or a regression has no output.
#
# The outputs become the new regressions, to be reviewed with `git diff` and committed:
# a missing regression is created, and a differing one is replaced if it has no
# uncommitted changes. A regression with uncommitted changes, e.g., an intended output
# written by hand, is kept. Running the tests again then shows only what is left.
#
# Usage: diff-regressions.sh SUITE_DIR REG_DIR

SUITE_DIR=$1
REG_DIR=$2

# whether the regression is committed and unchanged, so git can restore it
restorable() {
  git ls-files --error-unmatch "$1" > /dev/null 2>&1 && git diff --quiet HEAD -- "$1" 2> /dev/null
}

changed=()
kept=()
created=()
orphaned=()

for output in "$SUITE_DIR"/*.als "$SUITE_DIR"/*.js "$SUITE_DIR"/*.des.cfr "$SUITE_DIR"/*.html "$SUITE_DIR"/*.dot; do
  [ -f "$output" ] || continue
  reg="$REG_DIR/$(basename "$output").reg"
  if [ ! -f "$reg" ]; then
    cp "$output" "$reg"
    created+=("$reg")
  elif ! cmp -s "$reg" "$output"; then
    echo "--- $reg"
    echo "+++ $output"
    diff "$reg" "$output"
    if restorable "$reg"; then
      cp "$output" "$reg"
      changed+=("$reg")
    else
      kept+=("$reg")
    fi
  fi
done

for reg in "$REG_DIR"/*.reg; do
  [ -f "$reg" ] || continue
  output="$SUITE_DIR/$(basename "$reg" .reg)"
  [ -f "$output" ] || orphaned+=("$reg")
done

report() {
  local title=$1
  shift
  [ $# -eq 0 ] && return
  echo "$title ($#):"
  printf '  %s\n' "$@"
}

echo
report "Replaced by the new output" "${changed[@]}"
report "Kept, since they have uncommitted changes; the output differs" "${kept[@]}"
report "Created, since the output had no regression" "${created[@]}"
report "No output, e.g., of a removed or failing test model" "${orphaned[@]}"

total=$(( ${#changed[@]} + ${#kept[@]} + ${#created[@]} + ${#orphaned[@]} ))
if [ $total -gt 0 ]; then
  echo
  echo "[FAIL] $total regression(s) do not match: review them with git diff, commit them, and run the tests again."
  exit 1
fi
echo "[OK] All outputs match their regressions."
