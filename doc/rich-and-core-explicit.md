# The rich and the core explicit model

An explicit model is a Clafer model that the compiler does not transform any further:
compiled again, it prints itself. Clafer has two explicit models, both fixpoints:

| | `clafer -m clafer` | `clafer -m clafer --core` |
|---|---|---|
| name | rich explicit model | explicit core model |
| keeps | the modeling intent: enumerations, initializers, behavioral patterns, transitions | the core language only |
| for | reading, editing, storing, diffing; backends that use the intent | the meaning; what the backends solve |
| IR | the IR as resolved; `-m json` prints it | the IR after `lowerToCore`; `-m json --core` prints it |
| file | `model.des.cfr`, first line `//# OPTIONS --explicit` | `model.core.cfr`, first line `//# OPTIONS --explicit --core` |

Each file declares its options in its first line, so it compiles to itself without options on
the command line: `clafer -m clafer model.core.cfr` prints the core again.

Up to Clafer 0.5.8 there was one explicit model, in which everything that is not a default was
desugared: enumerations became clafers, initializers constraints, and behavioral patterns and
transitions LTL formulas. It showed what the backends solve, but the modeling intent was lost,
and the model was hard to read and to map back to what was written: for example,
`never p between q and r` was `G (((q && no r) && F r) => (no p U r))`.

## The principle of the core

**The explicit core model contains only the constructs that cannot be lowered into more
primitive forms of the Clafer language.** A construct that Clafer can write with other
constructs is not in the core: its lowering is. A construct stays in the core only when the
operators that its lowering needs are not in the language.

So the core is the smallest language in which every Clafer model can be written, and it is
what the semantics (kbak/clafer-semantics) has to define: every other construct is defined by
its lowering. The principle decides each construct:

| Construct | In the core | Why |
|---|---|---|
| `enum Color = red \| green` | no: an abstract clafer and a clafer for each literal | it is written with clafers |
| `final x`, `finalref x`, `finaltarget x` | no: constraints in `x` with `X` and `previous`, e.g., `[ all c : this \| X (c in parent.x) ]` and `[ all c : this \| previous (some parent) => previous (c in parent.x) ]` for the instances of a final `x` | they are written with the temporal operators |
| `initial x` | no: `[ initially (some this.x) ]` in the parent, `[ initially (some x) ]` at the top level | it is written with `initially` |
| the multiplicity of an abstract clafer, e.g., `abstract Tools 3..6` | no: `[ (#Tools >= 3) && (#Tools <= 6) ]` next to it, at the top level, or `#this.Tools` in the parent of a nested one, and `abstract Tools 0..*` | it is written with a constraint |
| behavioral patterns, e.g., `never p between q and r` | no: their LTL formula | they are written with `X`, `F`, `G`, `U`, `W` |
| transitions, e.g., `on --> off` | no: their LTL formula | as the patterns |
| `x -> T = e` | no: `[ some x => x.dref = e ]` in the parent | it is written with a constraint |
| `x -> T := e`, in a static model, per instance with a value without temporal operators, of a collection, or at time zero | no: a constraint, with `initially` in a temporal model | as `=` |
| `x -> T := e`, per instance, with a value with temporal operators | no: `[ all c : this.x \| (not previous (c in this.x)) => (c.dref = e) ]` in the parent | it is written with the past-time operator `previous` |

The last row was the one exception until 0.5.9. The value of such an initializer is evaluated
in the parent's context, when the instance appears (gsdlab/clafer#123). The core can write
`initially` only in the context of `x`, where the temporal operators of the value would mean
something else, and in the context of the parent, "the instance appears now" needs a
past-time operator: `not previous (c in this.x)`. Since Clafer has the past-time operators
(gsdlab/clafer#127), the `:=` is lowered to that constraint in the parent, which holds in every
state of the parent, so the core has no rich construct left (gsdlab/clafer#126). The past-time
operators themselves are core operators: `previous`, `once`, `historically`, `since` and
`triggered` (see the cheat sheet).

The defaults have a single obvious expansion, and both explicit models write them out, so the
rich explicit model loses no intent by them: the keyword multiplicities (`?`, `*`, `+`) and
group cardinalities (`xor`, `or`, `mux`, `opt`), the completion of paths (`x` is `this.x` or
`parent.x`), the automatic `dref`, `: integer` for `-> integer`, `-> 1` for `-> integer = 1`,
and the keywords `eventually`, `globally`, `next`, `until` and `weakuntil` for `F`, `G`, `X`,
`U` and `W`.

### Constructs kept in the core that could still be lowered

The principle is not applied to the end: a few constructs stay in the core for now, although
Clafer could write them with more primitive constructs.

- The anchors `initially p` and `finally p`: with the quantifier that captures the instance, as
  the finality modifiers use it, `initially p` in `x` is
  `[ all c : this | (not previous (c in this.parent.x)) => p' ]` and `finally p` is
  `[ all c : this | ((c in this.parent.x) && not X (c in this.parent.x)) => p' ]`, where `p'` is
  `p` with `c` for `this`; at the top level, "the first state" is `not previous` of a formula
  that always holds, which Clafer can write only awkwardly.
- The set reference `x -> T`: the bag reference `x ->> T` with
  `[ all disj a, b : this.x | a.dref != b.dref ]` in the parent.
- The multiplicity of a concrete clafer and the group cardinality: `0..*` with a constraint
  that counts the instances (`#this.x`), or the children that have one.

They are the structural and temporal vocabulary that the semantics defines directly, the
backends encode them natively (Choco's set variables, Alloy's multiplicities), and their
lowering would make the core much harder to read. Each lowering would follow the others: the
lowered constraint gets its `origin`, and a backend may keep encoding the construct
natively (see the pipeline).

## The pipeline

```
model.cfr ── parse, desugar the defaults, resolve ──▶ IR (rich) ──▶ -m clafer, -m json
                                                       │
                                               lowerToCore (Core.hs)
                                                       │
                                                       ▼
                                                   IR (core) ──▶ -m clafer --core, -m json --core
                                                       │
                                     ┌─────────────────┼─────────────────┐
                                     ▼                 ▼                 ▼
                               static Alloy      temporal Alloy        Choco
```

Every backend gets the core, so the explicit core model is exactly what they solve, and the
meaning of each rich construct has a single definition: its lowering, in
`Language.Clafer.Intermediate.Core` (and `Initializers` for the initializers). The backends
interpret only the constructs that remain in the core.

A backend may still use a rich form when it generates better code from it, as long as it
agrees with the lowering, which can be checked by comparing the instances, traces and
counterexamples of the two levels. The core IR keeps the trace back to the rich construct:
every clafer and constraint that a lowering made has its `origin` (`_cOrigin`, `_eOrigin`: the
construct and its position), also without `--record-provenance`, which only prints it. The
origin names the construct, not its arguments, so a backend that needs those reads the rich IR,
which `generate` has next to the core. One backend does this so far: the temporal Alloy
generator declares the relations of the clafers that are final with all their ancestors in the
rich IR without `var` (`staticClafers` in `Finality`), which the core constraints of the
finality modifiers allow. Static Alloy and Choco use
the core alone (the scopes of all backends are computed from the rich IR). Other backends could
do the same, e.g., an SMV backend for the patterns or a state machine view for the transitions.

## The rich constructs and their lowering

### Enumerations

`enum Color = red | green` is an abstract clafer with a concrete clafer `1..1` for each
literal, marked as an enumeration (`_enum` in the modifiers of the IR). The rich explicit
model prints the enumeration; the core prints the clafers:

```
enum Color = red | green                  // rich
abstract 0..* Color 0..* {}               // core
0..* red : Color 1..1 {}
0..* green : Color 1..1 {}
```

In a temporal model, the enumeration and its literals are final, in both.

### Initializers

`x -> T = e` and `x -> T := e` are an element of `x` in the IR (`IEInitializer`), with the
equation `x.dref = e` in the context of the parent of `x`. The rich explicit model prints
them after the multiplicity, with the clock of every `:=` (kbak/clafer-semantics#194), e.g.,
`0..* x -> int 0..1 := each this.A__y.dref + 1 {` and `0..* xs -> int 0..* := together 1 ++ 2 {}`,
so that its meaning does not depend on the multiplicity; an abstract clafer always has its
multiplicity, `0..*` when none was written. The core:

- `=`, and `:=` in a static model: `[ some x => x.dref = e ]` in the parent.
- `:= each e` of a concrete clafer with more than one instance under a parent, in a static
  model: `[ all c : this.xs | c.dref = e ]` in the parent, one equation for each instance,
  which `xs.dref = e` is not (`:= each 1, 2` has no instance, while two instances satisfy
  `xs.dref = 1, 2` together).
- `:=` of each instance, in a temporal model: `[ initially (this.dref = e') ]` in `x`, where
  `e'` is `e` with `this.parent` for `this`.
- `:=` of a set of instances (`xs -> T * := e`, kbak/clafer-semantics#170):
  `[ initially (some xs => xs.dref = e) ]` in the parent, also when `e` has temporal
  operators, since the parent is the context of `e`; for a top-level abstract clafer with `*`,
  `[ initially (some X => X.dref = e) ]` at the top level (time zero).
- `:=` of each instance, in a temporal model, when `e` has temporal operators:
  `[ all c : this.x | (not previous (c in this.x)) => (c.dref = e) ]` in the parent, with a
  name for `c` that no clafer has (`x_1`): each instance that appears, i.e., that was not an
  instance of `x` under the parent in the previous state, has the value of `e` in the
  parent's context then. The temporal Alloy output of `tmp_initialValue07` is equivalent to the
  interpretation of `:=` by the temporal Alloy generator of 0.5.8, which Alloy checks.

So the rich explicit model keeps every `=` and `:=` as written, and the core has none (test
case `CoreInitializers`). See
[initial-value.md](initial-value.md) for the meaning.

### Behavioral patterns

The patterns of Dwyer et al. (Patterns in Property Specifications for Finite-State
Verification, ICSE 1999), `never`, `sometime`, `lonce`, `always`, `s must precede p` and
`s must follow p`, in the scopes globally, `before r`, `after q`, `between q and r` and
`after q until r`, are operators of the IR, e.g., `never between` with the arguments
`p`, `q`, `r`. The core is their LTL formula.

The patterns and transitions in the rich and the core explicit model of a constraint:

```
[never ((#p) >= 1) between ((#q) >= 1) and ((#r) >= 1)]
[G (((((#q) >= 1) && ((#r) = 0)) && (F ((#r) >= 1))) => (((#p) = 0) U ((#r) >= 1)))]

[((#this.on) >= 1) --> ((#this.off) >= 1) --> ((#this.on) >= 1)]
[((#this.on) >= 1) => (X (((#this.off) >= 1) && (X ((#this.on) >= 1))))]
```

### Transitions

`a --> b`, `a -[g]-> b`, `a -->> b` and `a -[g]->> b`, and the transition of a clafer
(`on --> off`, which is `[ this --> off ]` in `on`), are operators of the IR; a chain
`a --> b --> c` is a sequence. The core is their LTL formula: `a --> b` is `a => X b`,
`a --> b --> c` is `a => X (b && X c)`, and `a -->> b` is `a => ((this && a) U b)`.

## Provenance

With `--record-provenance`, the explicit core model shows where each lowered construct comes
from: a comment after each clafer and constraint that a lowering made names the rich construct
and its position, `file:line:column` as in the messages, so that tools can find it; the line is
the one in its file, also in a model with imports. The file is its name only, without the
folders, which depend on where the compiler runs.

```
[((#Tools) >= 1) && ((#Tools) <= 3)] // abstract multiplicity, model.cfr:2:1
abstract 0..* Color 0..* {} // enum, model.cfr:1:1
0..* a 0..1 {
  0..* b 0..1 {
    [all b_1 : this | X (b_1 in this.parent.b)] // final, model.cfr:5:5
  }
}
0..* x -> int 1..1 {
  [initially (this.dref = 1)] // :=, model.cfr:6:1
}
```

The constructs are `enum`, `=`, `:=`, `initial`, `final`, `finalref`, `finaltarget`,
`abstract multiplicity`, `transition` and the patterns (e.g., `never before`). The IR records the
origin (`_cOrigin` of a clafer, `_eOrigin` of a constraint, with the position in the file, in
`-m json --core`). The flag is off by default: the comments are for reading the core against
the model, and the core without them is what the backends get. A comment does not change the
model, so the core with comments compiles to the same core: the positive suite checks it without
the comments, and keeps the cores with them as regressions (`*.core.cfr.reg`), for review.

## Checks

- Each rich and each core explicit model of the test models compiles to itself (the positive
  suite validates both, `-m clafer` and `-m clafer --core`), and both are regressions,
  `test/regression/*.des.cfr.reg` and `*.core.cfr.reg`, so a change of a lowering shows in the
  core directly. An abstract clafer is `0..*` in the core, whose bound is a constraint: one
  that the optimizer gives no instances (`0..0`, nothing extends it) was printed with `0..0`,
  which the next compilation read as a bound, so the core of 18 test models was not a
  fixpoint.
- Before 0.5.9 lowered the temporal modifiers and the multiplicities of abstract clafers, the
  core of each test model was the explicit model that Clafer 0.5.8, which desugared everything,
  printed for it, except for a `:=` whose value has temporal operators (`tmp_initialValue07`),
  which 0.5.8 kept and 0.5.9 lowers with `previous`.
- The pattern expansions are verified: for every pattern and scope, nuXmv checks that the
  formula of the core is equivalent, on all traces, to a reference written from the
  definition of the pattern with past-time operators. All 30 pairs of pattern and scope are
  equivalent ([`test/patterns/check-patterns.py`](../test/patterns/check-patterns.py)); for
  example, `never p before r` is `F r => (no p U r)` in the core, and its reference is
  `F r -> G (!(O r) -> !p)`: if r occurs, no p before its first occurrence. Each reference is
  also written as a Clafer constraint with the past-time operators, compiled, and checked
  equivalent to itself, and the encoding of the past-time operators in the temporal Alloy
  output is proved against a definition of each operator by recursion on the states (also in
  Alloy, bounded: [`test/patterns/past-encoding.als`](../test/patterns/past-encoding.als)).
- `RichAndCoreExplicit` and `CoreInitializers` (test-suite) check the rich constructs in both
  models.

## Open points

1. **The temporal modifiers are lowered** since 0.5.9: `final`, `finalref` and `finaltarget`
   (kbak/clafer-semantics#192, "Language.Clafer.Intermediate.Finality"). Each keeps a set from
   one state to the next while the parent exists, without additions (`previous`) and without
   losses (`X`). The constraints are in the context of the clafer, where a quantifier captures
   the instance: `this` is empty in a state in which the instance does not exist. The temporal
   Alloy output of the test models is equivalent to the one of 0.5.8 (Alloy, up to 10 states).
   The temporal Alloy generator still declares the relations of the clafers that are final with
   all their ancestors in the rich IR without `var`, which the constraints allow: a backend may
   use the rich construct when it agrees with its lowering. `initial x` is
   `[ initially (some this.x) ]` in the parent (kbak/clafer-semantics#195): the parent has an
   `x` in the first state of each of its lifetimes, and the model at the start of the trace at
   the top level. The temporal Alloy output is the same formula as in 0.5.8, as a fact of its
   own. The anchors `initially` and `finally` stay in the core for now, although they could be
   lowered, as the semantics does ("present now and not present in the previous state"), with
   the quantifier that captures the instance, as for the finality modifiers (see "Constructs
   kept in the core that could still be lowered").
2. **The clock of `:=` has a syntax of its own since 0.5.9:** `:= each` and `:= together`
   (kbak/clafer-semantics#194). Before, a written `*` or `0..*` made `:=` a set initializer
   (kbak/clafer-semantics#170), and the rich explicit model left the multiplicity of an
   abstract clafer with a per-instance `:=` out, so that the meaning depended on a missing
   token. Now the rich explicit model writes the clock of every `:=` and every multiplicity.
3. **Consumers of the IR and of the explicit model:** the JSON output of the rich IR has the
   operators of the rich constructs, the initializers and the `_enum` modifier, and a consumer
   that does not read them can use `-m json --core`; chocosolver's explicit parser does not read `:=`,
   `=`, patterns or transitions on a declaration, so it reads the core.
4. **The semantics** (kbak/clafer-semantics) defines the core; the rich constructs are
   defined by their lowering, which the semantics may state, e.g., as theorems that each
   pattern's formula meets its definition.
