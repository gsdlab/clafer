#!/usr/bin/env python3
"""Proves that clafer's expansions of the behavioral patterns are right, with nuXmv.

For every pattern and scope, the script compiles a model with the pattern on the atoms
p, q, r and s (optional top-level clafers, so that each can hold or not in every state)
with `clafer -m clafer --core`, which prints the LTL formula that the backends get. It
then checks with nuXmv, over all traces of the four atoms, that the formula is equivalent
to a reference written here from the definitions of the patterns in words, with past-time
operators instead of the nested untils of the expansions. nuXmv proves the equivalence
(LTL model checking is complete), or prints a trace on which the two differ.

Needs a clafer with --core and nuXmv (https://nuxmv.fbk.eu). It is not part of `make test`;
run it after changing the expansions of the patterns, e.g., from the root of the repository:

    test/patterns/check-patterns.py --clafer $(cabal list-bin clafer)

Usage: check-patterns.py [--clafer PATH] [--nuxmv PATH] [--keep DIR]
"""

import argparse
import os
import re
import subprocess
import sys
import tempfile

# The scope of a pattern, as positions of the trace (Dwyer et al., ICSE 1999):
#   globally           every position
#   before r           the positions before the first r, if r occurs
#   after q            the positions from the first q on
#   between q and r    each interval from a q (without r) up to the next r, if r occurs
#   after q until r    each interval from a q (without r) up to the next r, or forever
#
# In the references, START is a q without r, OPEN holds inside an interval of between or
# after-until (since the latest START, no r), and CLOSED requires the interval to end with r.
START = "(q & !r)"
OPEN = f"(!r S {START})"            # at a position of an interval, from some START, without r since
SINCE_LAST_START = f"!{START} S"    # x since the latest START: (SINCE_LAST_START s) at p

# lonce: p becomes true at most once (one block of p) in each interval;
# BLOCKS holds at a p that ends a second block in the interval of some START
BLOCKS = f"(p & !r & Y (!r S (!p & !r & (!r S (p & !r & {OPEN})))))"

REFERENCES = {
    # absence
    ("never", ""): "G !p",
    ("never", "before"): "F r -> G ((!O r) -> !p)",
    ("never", "after"): "G ((O q) -> !p)",
    ("never", "between"): f"G (({OPEN} & F r) -> !p)",
    ("never", "after until"): f"G ({OPEN} -> !p)",
    # universality
    ("always", ""): "G p",
    ("always", "before"): "F r -> G ((!O r) -> p)",
    ("always", "after"): "G ((O q) -> p)",
    ("always", "between"): f"G (({OPEN} & F r) -> p)",
    ("always", "after until"): f"G ({OPEN} -> p)",
    # existence: a p in the scope, in every interval
    ("sometime", ""): "F p",
    ("sometime", "before"): "F r -> F (p & !O r)",
    ("sometime", "after"): "F q -> F (p & O q)",
    # an r that closes an interval: since the latest START (without r since), a p
    ("sometime", "between"): f"G ((r & Y {OPEN}) -> Y ({SINCE_LAST_START} (p & !r)))",
    ("sometime", "after until"): f"G ((r & Y {OPEN}) -> Y ({SINCE_LAST_START} (p & !r))) & G (({START} & G !r) -> F p)",
    # bounded existence: at most one block of p
    ("lonce", ""): "!F (p & F (!p & F p))",
    ("lonce", "before"): "F r -> !F (p & F (!p & F (p & !O r)))",
    ("lonce", "after"): "!F (O q & p & F (!p & F p))",
    ("lonce", "between"): f"G !({BLOCKS} & F r)",
    ("lonce", "after until"): f"G !{BLOCKS}",
    # precedence, s must precede p: every p in the scope has an s at or before it, in the scope
    ("precede", ""): "G (p -> O s)",
    ("precede", "before"): "F r -> G ((p & !O r) -> O s)",
    ("precede", "after"): "G ((p & O q) -> O (s & O q))",
    ("precede", "between"): f"G ((p & {OPEN} & F r) -> ({SINCE_LAST_START} s))",
    ("precede", "after until"): f"G ((p & {OPEN}) -> ({SINCE_LAST_START} s))",
    # response, s must follow p: every p in the scope has an s at or after it, in the scope
    ("follow", ""): "G (p -> F s)",
    ("follow", "before"): "F r -> G ((p & !O r) -> F (s & !O r))",
    ("follow", "after"): "G ((p & O q) -> F s)",
    ("follow", "between"): f"G ((p & {OPEN} & F r) -> (!r U (s & !r)))",
    ("follow", "after until"): f"G ((p & {OPEN}) -> (!r U (s & !r)))",
}

SCOPES = {"": "", "before": " before r", "after": " after q",
          "between": " between q and r", "after until": " after q until r"}


def clafer_pattern(kind, scope):
    pattern = f"s must {kind} p" if kind in ("precede", "follow") else f"{kind} p"
    return pattern + SCOPES[scope]


# --- the explicit core expressions, which clafer writes with every operand in parentheses

TOKEN = re.compile(r"\s*(\(#[a-z]\) >= 1|\(#[a-z]\) = 0|<=>|=>|&&|\|\||!|\(|\)|[UWFGX]\b)")


def tokens(text):
    pos, out = 0, []
    text = text.strip()
    while pos < len(text):
        m = TOKEN.match(text, pos)
        if not m:
            raise ValueError(f"cannot read {text[pos:]!r} in {text!r}")
        out.append(m.group(1))
        pos = m.end()
    return out


def to_smv(text):
    """The SMV formula of an explicit core expression over the atoms."""
    toks = tokens(text)
    pos = 0

    def operand():
        nonlocal pos
        t = toks[pos]
        pos += 1
        if t.startswith("(#"):  # (#p) >= 1 is p, (#p) = 0 is !p
            return t[2] if t.endswith(">= 1") else f"!{t[2]}"
        if t == "(":
            e = expression()
            assert toks[pos] == ")", toks[pos:]
            pos += 1
            return f"({e})"
        if t in ("!", "F", "G", "X"):
            return f"{t} {operand()}"
        raise ValueError(f"unexpected {t!r} in {text!r}")

    def expression():
        nonlocal pos
        left = operand()
        if pos < len(toks) and toks[pos] in ("<=>", "=>", "&&", "||", "U", "W"):
            op = toks[pos]
            pos += 1
            right = operand()
            if op == "W":  # nuXmv has no weak until: a W b is b V (a | b)
                return f"({right} V ({left} | {right}))"
            return f"{left} {dict({'<=>': '<->', '=>': '->', '&&': '&', '||': '|'}).get(op, op)} {right}"
        return left

    e = expression()
    assert pos == len(toks), toks[pos:]
    return e


def expansion(clafer, workdir, kind, scope):
    name = re.sub(r"\W", "_", f"{kind}_{scope}") or kind
    model = os.path.join(workdir, f"{name}.cfr")
    with open(model, "w") as f:
        f.write("p ?\nq ?\nr ?\ns ?\n\n")
        f.write(f"assert [ {clafer_pattern(kind, scope)} ]\n")
    out = subprocess.run([clafer, "-m", "clafer", "--core", "-o", "-s", model],
                         capture_output=True, text=True)
    if out.returncode != 0:
        raise RuntimeError(f"clafer failed on {model}:\n{out.stdout}{out.stderr}")
    asserts = [l for l in out.stdout.splitlines() if l.startswith("assert [")]
    if len(asserts) != 1:
        raise RuntimeError(f"no assertion in the core of {model}:\n{out.stdout}")
    return name, asserts[0][len("assert ["):-1]


def check(nuxmv, workdir, name, formula, reference):
    smv = os.path.join(workdir, f"{name}.smv")
    with open(smv, "w") as f:
        f.write("MODULE main\nVAR\n  p : boolean;\n  q : boolean;\n  r : boolean;\n  s : boolean;\n")
        f.write(f"LTLSPEC NAME equivalent := ({formula}) <-> ({reference})\n")
    out = subprocess.run([nuxmv, smv], capture_output=True, text=True)
    if "is true" in out.stdout:
        return True, ""
    if "is false" in out.stdout:
        trace = out.stdout[out.stdout.index("is false"):]
        return False, trace
    raise RuntimeError(f"nuXmv failed on {smv}:\n{out.stdout}{out.stderr}")


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--clafer", default="clafer")
    parser.add_argument("--nuxmv", default="nuXmv")
    parser.add_argument("--keep", help="keep the models and SMV files in this directory")
    args = parser.parse_args()
    workdir = args.keep or tempfile.mkdtemp(prefix="patterns-")
    os.makedirs(workdir, exist_ok=True)
    failures = 0
    for (kind, scope), reference in REFERENCES.items():
        name, core = expansion(args.clafer, workdir, kind, scope)
        formula = to_smv(core)
        ok, trace = check(args.nuxmv, workdir, name, formula, reference)
        print(f"{'OK  ' if ok else 'DIFF'} {clafer_pattern(kind, scope)}")
        if not ok:
            failures += 1
            print(f"     clafer:    {core}\n     smv:       {formula}\n     reference: {reference}")
            print("     " + "\n     ".join(trace.splitlines()[:60]))
    print(f"{len(REFERENCES) - failures} of {len(REFERENCES)} expansions are equivalent to the references")
    sys.exit(1 if failures else 0)


if __name__ == "__main__":
    main()
