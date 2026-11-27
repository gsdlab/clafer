#!/bin/bash
# Check 2: the core of the rich explicit model is the core of the model. For each model P.cfr
# of the positive test suite, clafer -m clafer --core on P.des.cfr gives P.core.cfr, without the
# provenance comments (as withoutOrigins removes them), since the rich model has no positions of
# P.cfr. Needs the outputs of compile-positive.sh. Fails, after all the models, if one differs,
# and names them with their differences.
#
# Usage: check-rich-to-core.sh SUITE_DIR JOBS CLAFER [CLAFER_ARGS...]

SUITE_DIR=$1
JOBS=$2
shift 2

WORK=$(mktemp -d)
trap 'rm -r "$WORK"' EXIT
touch "$WORK/failed"
export WORK

# check CLAFER [CLAFER_ARGS...] P.des.cfr: xargs appends the model
check() {
  local rich=${!#} name core dir
  name=$(basename "$rich" .des.cfr)
  core=$(dirname "$rich")/$name.core.cfr
  [ -f "$core" ] || return 0
  dir=$(mktemp -d "$WORK/model.XXXXXX")
  cp "$rich" "$dir/$name.des.cfr"
  if ! "${@:1:$#-1}" -m clafer --core "$dir/$name.des.cfr" > "$dir/log" 2>&1; then
    flock "$WORK/failed" bash -c 'echo "$0: the rich model does not compile"; cat "$1"; echo "$0" >> "$WORK/failed"' "$rich" "$dir/log"
    return 0
  fi
  local strip='s# // [^"]*[0-9]+:[0-9]+$##'
  if ! diff <(sed -E "$strip" "$core") <(sed -E "$strip" "$dir/$name.des.core.cfr") > "$dir/diff"; then
    flock "$WORK/failed" bash -c 'echo "$0: the core of the rich model differs (< core, > core of the rich model)"; cat "$1"; echo "$0" >> "$WORK/failed"' "$rich" "$dir/diff"
  fi
}
export -f check

find "$SUITE_DIR" -type f -iname "*.des.cfr" -print0 | sort -z |
  xargs -0 -n 1 -P "$JOBS" bash -c 'check "$@"' check "$@"

if [ -s "$WORK/failed" ]; then
  echo
  echo "[FAIL] Models whose rich model does not give their core:"
  sort "$WORK/failed" | sed 's/^/  /'
  exit 1
fi
echo "Check 2: the rich model of every model gives its core."
