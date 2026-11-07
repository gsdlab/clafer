#!/bin/bash
# Compiles the models of the positive test suite to all outputs and validates the outputs
# (clafer -v), JOBS models at a time. The messages of each model are printed together when
# it is done. Fails, after all the models, if one fails to compile or an output fails to
# validate, and names them; a counterexample is not a failure.
#
# Usage: compile-positive.sh SUITE_DIR JOBS CLAFER [CLAFER_ARGS...]

SUITE_DIR=$1
JOBS=$2
shift 2

WORK=$(mktemp -d)
trap 'rm -r "$WORK"' EXIT
touch "$WORK/failed"
export WORK

# compile CLAFER [CLAFER_ARGS...] MODEL: xargs appends the model
compile() {
  local model=${!#} log
  log=$(mktemp "$WORK/log.XXXXXX")
  if ! "${@:1:$#-1}" "$model" > "$log" 2>&1; then
    flock "$WORK/failed" bash -c 'echo "$0" >> "$WORK/failed"' "$model"
  fi
  # one model's messages at a time
  flock "$WORK/failed" cat "$log"
  rm "$log"
}
export -f compile

find "$SUITE_DIR" -type f \( -iname "*.cfr" ! -iname "*.des.cfr" \) -print0 | sort -z |
  xargs -0 -n 1 -P "$JOBS" bash -c 'compile "$@"' compile "$@"

if [ -s "$WORK/failed" ]; then
  echo
  echo "[FAIL] Models that fail to compile or whose outputs fail to validate:"
  sort "$WORK/failed" | sed 's/^/  /'
  exit 1
fi
