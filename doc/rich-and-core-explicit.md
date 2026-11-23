# The rich and the core explicit model

An explicit model is a Clafer model that the compiler does not transform any further:
compiled again, it prints itself. Clafer has two explicit models, both fixpoints:

| | `clafer -m clafer` | `clafer -m clafer --core` |
|---|---|---|
| name | rich explicit model | explicit core model |
| keeps | the modeling intent: enumerations, initializers, behavioral patterns, transitions | the core language only |
| for | reading, editing, storing, diffing; what the backends read (see [the roles](#the-roles-of-the-two-models)) | the meaning: explaining each construct, and the oracle for the backends |
| IR | the IR as resolved; `-m json` prints it | the IR after `lowerToCore`; `-m json --core` prints it |
| file | `model.des.cfr`, first line `//# OPTIONS --explicit` | `model.core.cfr`, first line `//# OPTIONS --explicit --core` |

Each file declares its options in its first line, so it compiles to itself without options on
the command line: `clafer -m clafer model.core.cfr` prints the core again.

Up to Clafer 0.5.8 there was one explicit model, in which everything that is not a default was
desugared: enumerations became clafers, initializers constraints, and behavioral patterns and
transitions LTL formulas. It showed what the backends solve, but the modeling intent was lost,
and the model was hard to read and to map back to what was written: for example,
`never p between q and r` was `G (((q && no r) && F r) => (no p U r))`.

## The roles of the two models

Decided for 0.6.0 (kbak/clafer-semantics#200; the design is in clafer-tools'
`design/explicit-core.md`):

- **The rich explicit model is what the backends read.** Each backend lowers it to what it
  encodes best: the backends' capabilities are not nested (Choco has no temporal logic, Alloy
  bounds the traces, SMV is finite-state), so no single lowered level suits all of them, and
  a core lowered for one backend would take from the others the constructs they encode
  natively, e.g., enumerations and finality. There are no lowering profiles: a backend that
  has no native encoding of a construct uses that construct's lowering.
- **The explicit core model is the full lowering, for explaining the meaning.** Every
  construct whose meaning Clafer defines is replaced by its definition, written in a
  vocabulary whose meaning the reader already knows ([below](#the-principle-of-the-core)). It
  is also the oracle: for any backend, the rich and the core model of a model must give the
  same instances, traces and counterexamples, and a second implementation of the lowering (the
  planned Java frontend) must print the same core.
- **The origin is for tracing, not for recovering the intent.** It maps the core back to the
  rich construct and its position, for messages, unsat cores and the IDE.

The backends of the Haskell compiler still get the core IR (see [the pipeline](#the-pipeline)),
which is correct, since the core is a subset of the rich language; the Java toolchain
reads the rich model.

## The principle of the core

"Lower everything that can be lowered" has no useful end: `a => b` is `!a || b`, and
`once p` is `true since p`. The semantics does lower that far: `Formula.lower`
(kbak/clafer-semantics, `Clafer/Behavioral/Lowering.lean`) leaves only `not`, `and`, `or`,
`next`, `eventually`, `always`, `strongUntil`, `weakUntil`, `previous`, `since` and the
quantifiers, with a lifetime guard on every temporal operator, which is a normal form for
proofs. Printed as Clafer it would explain nothing about Clafer: those rewrites are
equivalences of the logic, not definitions of Clafer. So the core follows the semantics in
*which constructs are lowered*, not operator by operator, by a criterion with two parts.

**1. The vocabulary of the core is fixed in advance.** It is the formalisms on which the
Clafer papers and the formalization build, whose meaning a reader is assumed to know:

- **Structure, as in class and feature modeling:**
  - clafers with containment and inheritance
  - multiplicities (as in UML)
  - group cardinalities (as in cardinality-based feature models)
  - set and bag references (unique and non-unique association ends)

  These are the primitives of the structural semantics (`Reference.set` and `.bag`,
  `Multiplicity`, `GroupCard`).
- **Relational first-order logic with arithmetic, as in Alloy:**
  - navigation and the set operators
  - membership and the comparisons
  - all the connectives: `!`, `&&`, `||`, `=>`, `<=>`, `xor`, `if then else`
  - the quantifiers and `let`
  - `#`, `sum`, `product`, `min`, `max`
- **Linear temporal logic with past, as in Alloy 6 and nuXmv:** `F`, `G`, `X`, `U`, `W`,
  `previous`, `once`, `historically`, `since`, `triggered`.
- **One evaluation rule:** a constraint holds for each instance of its context, and its
  temporal operators range over the lifetime of that instance. It is stated once, as the
  meaning of the core, not lowered at each operator.

In the formalization this is the level of `Formula` (`Clafer/Behavioral/Formula.lean`),
without `initially` and `finally`, over the structural core.

**2. Every construct outside the vocabulary is lowered into it, and nothing inside it is.**
- A construct outside the vocabulary is specific to Clafer: its meaning is defined in terms
  of the vocabulary, the core replaces it with that definition, and so the core explains it.
- A construct that the literature defines as an abbreviation for formulas of the logic is
  outside, even when it is standard. Dwyer's patterns are LTL templates. Enumerations are
  an abstract clafer with `1..1` literal clafers, as Alloy defines its `enum` too.

The criterion decides each construct:

| Construct | In the core | Why |
|---|---|---|
| `enum Color = red \| green` | no: an abstract clafer and a clafer for each literal | an abbreviation for clafers |
| `final x`, `finalref x`, `finaltarget x` | no: constraints in `x` with `X` and `previous`, e.g., `[ all c : this \| X (c in parent.x) ]` and `[ all c : this \| previous (some parent) => previous (c in parent.x) ]` for the instances of a final `x` | stability over a lifetime, defined with the temporal operators |
| `initial x` | no: `[ initially (some this.x) ]` in the parent, `[ initially (some x) ]` at the top level | defined with `initially` |
| the multiplicity of a top-level abstract clafer, e.g., `abstract Tools 3..6` | no: `[ (#Tools >= 3) && (#Tools <= 6) ]` next to it, and `abstract Tools 0..*` | a global count over all the instances of its subclafers, defined with a constraint |
| the multiplicity of a nested abstract clafer | yes (0.6.0 still lowers it to `#this.Tools` in the parent, see [below](#where-the-core-of-060-differs-from-the-criterion)) | an ordinary multiplicity, counted over the instances of its subclafers |
| `initially p`, `finally p` | no (0.6.0 still keeps them, see [below](#where-the-core-of-060-differs-from-the-criterion)) | anchored to the lifetime of an instance |
| behavioral patterns, e.g., `never p between q and r` | no: their LTL formula | LTL templates |
| transitions, e.g., `on --> off` | no: their LTL formula | as the patterns |
| `x -> T = e` | no: `[ some x => x.dref = e ]` in the parent | defined with a constraint |
| `x -> T := e`, in a static model, per instance with a value without temporal operators, of a collection, or at time zero | no: a constraint, with `initially` in a temporal model | as `=` |
| `x -> T := e`, per instance, with a value with temporal operators | no: `[ all c : this.x \| (not previous (c in this.x)) => (c.dref = e) ]` in the parent | defined with the past-time operator `previous` |
| concrete multiplicities, group cardinalities, set and bag references | yes | the structural vocabulary |
| the connectives, quantifiers, temporal and past-time operators | yes | the logic of the vocabulary |

The last row was the one exception until 0.6.0. The value of such an initializer is evaluated
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

### When the core is finished

The criterion makes it checkable:

- the core has no construct outside the vocabulary;
- every rich construct has its lowering here and a theorem in the semantics that defines its
  meaning, e.g., `expandAnchors_agrees`, `Modifiers.stable_iff_adjacent`,
  `Initializers.expansion_agrees`, `Chain.expand_agrees` and
  `AbstractMultiplicity.valid_iff_global`;
- lowering a core model changes nothing.

A new construct is then either inside the vocabulary, a primitive with its own meaning in
the semantics, or outside it, with its lowering and the theorem.

### Where the core of 0.6.0 differs from the criterion

- **The anchors `initially p` and `finally p` are kept, but they are outside the
  vocabulary:** they anchor `p` to the lifetime of the instance, not to the start of the
  trace. They are to be lowered, as the semantics does (`expandAnchors`: the instance is
  present now and was not present in the previous state), with the quantifier that captures
  the instance, as for the finality modifiers:
  - `initially p` in `x` is `[ all c : this | (not previous (c in this.parent.x)) => p' ]`;
  - `finally p` is `[ all c : this | ((c in this.parent.x) && not X (c in this.parent.x)) => p' ]`;

  where `p'` is `p` with `c` for `this`.

  At the top level, the context is the root, which lives in every state, so its only birth is
  the first state of the trace, as in the semantics (`Trace.Starts`, `root_live`). Its "not
  present in the previous state" is "not `previous` of a formula that always holds":
  - `initially p` at the top level is `[ (!(previous (some root))) => p ]`;
  - `finally p` at the top level has no birth or death to anchor to, since the root never
    dies: it holds vacuously, as `Trace.Ends` has no end for a permanent life.

  The temporal Alloy generator already writes the top-level `initially p` this way
  (`(not before some root) implies p`). Alloy checks that the two are equivalent: each
  implies the other on every trace. `initial x` is then lowered through the anchors.
- **The multiplicity of a nested abstract clafer is lowered, but it is inside the
  vocabulary,** so it is to stay in the core as a multiplicity. It is an ordinary per-parent
  multiplicity, counted over the instances of all its subclafers, as a UML property typed by
  an abstract class counts the instances of all its subclasses. The semantics shows it
  (`AbstractMultiplicity.nested`, `valid_iff_global`): structural validity already enforces
  a nested abstract bound, and only the top-level one adds an obligation. The written
  bound is then the only multiplicity of an abstract clafer in the IR, as the semantics'
  `authoredMultiplicity` is: the optimizer no longer gives an abstract clafer that nothing
  extends `0..0` (see [the pipeline](#the-pipeline)).

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

In this compiler every backend gets the core, so the explicit core model is exactly what they
solve (the Java toolchain will read the rich model instead, see
[the roles](#the-roles-of-the-two-models)), and the meaning of each rich construct has a single
definition: its lowering, in
`Language.Clafer.Intermediate.Core` (and `Initializers` for the initializers). The backends
interpret only the constructs that remain in the core.

A backend may still use a rich form when it generates better code from it, as long as it
agrees with the lowering, which can be checked by comparing the instances, traces and
counterexamples of the two levels. The core IR keeps the trace back to the rich construct:
every clafer and constraint that a lowering made has its `origin` (`_cOrigin`, `_eOrigin`: the
construct and its position), also without `--record-provenance`, which only prints it. The
origin names the construct, not its arguments, so a backend that needs those reads the rich IR,
which `generate` has next to the core. The temporal Alloy generator does this twice: it declares
the relations of the clafers that are final with all their ancestors in the rich IR without
`var` (`staticClafers` in `Finality`), which the core constraints of the finality modifiers
allow, and it encodes the literals of an enumeration as constants (`enumLiterals` in `Core`):
a `one sig` without a parent relation, whose finality constraints, which hold trivially, it
leaves out by their origin. Static Alloy and Choco use the core alone. The scopes of all the
backends are computed from the rich IR: the multiplicities of the abstract clafers, the set
references and the counting constraints as written. Other backends could
do the same, e.g., an SMV backend for the patterns or a state machine view for the transitions.

Consumers outside the compiler read either level:
- The JSON output of the rich IR (`-m json`) has the operators of the rich constructs, the
  initializers and the `_enum` modifier. A consumer that does not read them uses
  `-m json --core`.
- chocosolver's explicit parser does not yet read the rich constructs (`=`, `:=`, the
  patterns, the transitions), so it reads the static core.

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

The clock is written because, without it, a written `*` or `0..*` made `:=` a set initializer
(kbak/clafer-semantics#170). The rich explicit model then had to leave out the multiplicity of
an abstract clafer with a per-instance `:=`, so its meaning depended on a missing token.

### Temporal modifiers

`final`, `finalref` and `finaltarget` (kbak/clafer-semantics#192,
`Language.Clafer.Intermediate.Finality`) each keep a set from one state to the next while the
parent exists, without additions (`previous`) and without losses (`X`). The constraints are in
the context of the clafer, where a quantifier captures the instance, since `this` is empty in a
state in which the instance does not exist. The temporal Alloy output of the test models is
equivalent to the one of 0.5.8 (Alloy, up to 10 states).

`initial x` is `[ initially (some this.x) ]` in the parent (kbak/clafer-semantics#195): the
parent has an `x` in the first state of each of its lifetimes. At the top level, the model has
an `x` at the start of the trace. The temporal Alloy output is the same formula as in 0.5.8, as
a fact of its own.

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
- Before 0.6.0 lowered the temporal modifiers and the multiplicities of abstract clafers, the
  core of each test model was the explicit model that Clafer 0.5.8, which desugared everything,
  printed for it, except for a `:=` whose value has temporal operators (`tmp_initialValue07`),
  which 0.5.8 kept and 0.6.0 lowers with `previous`.
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

These are decided, and to be done for 0.6.0:

1. **Lower the anchors** in `Core.hs`, nested and at the top level, and `initial x` through
   them (see
   [Where the core of 0.6.0 differs from the criterion](#where-the-core-of-060-differs-from-the-criterion)).
   The explicit core then has no `initially` or `finally`, and its fixpoint check covers
   `some root` in a core model.
2. **Keep a nested abstract multiplicity in the core**, as a multiplicity. Only a top-level
   abstract multiplicity is lowered to a `#` constraint.
3. **The optimizer does not set `0..0`.** Whether an abstract clafer that nothing extends has
   instances is the backend's choice: Alloy gives an abstract signature without extensions
   atoms of its own, so the Alloy backend gives such a clafer no instances; chocosolver's
   abstract clafers have only the instances of their subclafers. The IR, the explicit models
   and the JSON output keep the multiplicity as written.
4. **The print of the core is a contract.** The planned Java lowering must print the same core
   as `Core.hs`, so these are to be written down:
   - the names of the generated clafers and quantifier variables
   - the place and order of the lowered elements
   - the parentheses
   - the provenance comments
5. **Print `real` and `double` in both explicit models.** `-m clafer` prints none for a model
   with a reference to a real or a double, because the walk it shares with the Choco output
   refuses them. The explicit models write everything out, whether a backend solves it or
   not: the references, the literals, and their ranges in the scope file.
