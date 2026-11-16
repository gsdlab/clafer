# The rich and the core explicit model

An explicit model is a Clafer model that the compiler does not transform any further:
compiled again, it prints itself. Clafer has two explicit models, both fixpoints:

| | `clafer -m clafer` | `clafer -m clafer --core` |
|---|---|---|
| name | rich explicit model | explicit core model |
| keeps | the modeling intent: enumerations, initializers, behavioral patterns, transitions | the core language only |
| for | reading, editing, storing, diffing; backends that use the intent | the meaning; what the backends solve |
| IR | the IR as resolved, also the JSON output (`-m json`) | the IR after `lowerToCore` |

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
| behavioral patterns, e.g., `never p between q and r` | no: their LTL formula | they are written with `X`, `F`, `G`, `U`, `W` |
| transitions, e.g., `on --> off` | no: their LTL formula | as the patterns |
| `x -> T = e` | no: `[ some x => x.dref = e ]` in the parent | it is written with a constraint |
| `x -> T := e`, in a static model, per instance with a value without temporal operators, of a collection, or at time zero | no: a constraint, with `initially` in a temporal model | as `=` |
| `x -> T := e`, per instance, with a value with temporal operators | **yes** | its lowering needs a past-time operator, which Clafer does not have |

The last row is the one exception today. The value of such an initializer is evaluated in the
parent's context, when the instance appears (gsdlab/clafer#123). The core can write
`initially` only in the context of `x`, where the temporal operators of the value would mean
something else, and in the context of the parent, "the instance appears now" needs a
past-time operator: `not previous (c in this.x)`. Clafer has no past-time operators, so this
`:=` cannot be lowered and stays in the core, which marks it. When Clafer has them
(gsdlab/clafer#127), the principle moves it out of the core: it becomes
`[ G (all c : this.x | (not previous (c in this.x)) => (c.dref = e)) ]` in the parent
(gsdlab/clafer#126).

The defaults have a single obvious expansion, and both explicit models write them out, so the
rich explicit model loses no intent by them: the keyword multiplicities (`?`, `*`, `+`) and
group cardinalities (`xor`, `or`, `mux`, `opt`), the completion of paths (`x` is `this.x` or
`parent.x`), the automatic `dref`, `: integer` for `-> integer`, `-> 1` for `-> integer = 1`,
and the keywords `eventually`, `globally`, `next`, `until` and `weakuntil` for `F`, `G`, `X`,
`U` and `W`.

## The pipeline

```
model.cfr ── parse, desugar the defaults, resolve ──▶ IR (rich) ──▶ -m clafer, -m json
                                                       │
                                               lowerToCore (Core.hs)
                                                       │
                                                       ▼
                                                   IR (core) ──▶ -m clafer --core
                                                       │
                                     ┌─────────────────┼─────────────────┐
                                     ▼                 ▼                 ▼
                               static Alloy      temporal Alloy        Choco
```

Every backend gets the core, so the explicit core model is exactly what they solve, and the
meaning of each rich construct has a single definition: its lowering, in
`Language.Clafer.Intermediate.Core` (and `Initializers` for the initializers). The backends
interpret the constructs that remain in the core: the temporal Alloy generator interprets the
per-instance `:=` with a temporal value, and the static backends never get it, since in a
static model `:=` is `=`. A backend that can use the intent, such as an SMV backend for the
patterns or a state machine view for the transitions, may read the rich IR instead; it must
then agree with the lowering, which can be checked by comparing the instances, traces and
counterexamples of the two levels.

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
them after the multiplicity, e.g., `0..* x -> int 0..1 := this.A__y.dref + 1 {`. The core:

- `=`, and `:=` in a static model: `[ some x => x.dref = e ]` in the parent.
- `:=` of each instance, in a temporal model: `[ initially (this.dref = e') ]` in `x`, where
  `e'` is `e` with `this.parent` for `this`.
- `:=` of a set of instances (`xs -> T * := e`, kbak/clafer-semantics#170):
  `[ initially (some xs => xs.dref = e) ]` in the parent, also when `e` has temporal
  operators, since the parent is the context of `e`; for a top-level abstract clafer with `*`,
  `[ initially (some X => X.dref = e) ]` at the top level (time zero).
- `:=` of each instance, in a temporal model, when `e` has temporal operators: `:=` itself,
  the exception of the principle. The temporal Alloy generator gives each instance, in the
  first state of each of its lifetimes, the value evaluated in the parent's context.

So the rich explicit model keeps every `=` and `:=` as written, and the core keeps only the
`:=` that cannot be lowered (test case `CoreInitializers`). See
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

## Checks

- Each rich and each core explicit model of the test models compiles to itself, and the core
  of each test model is the explicit model that Clafer 0.5.8, which desugared everything,
  printed for it, except for a `:=` whose value has temporal operators (`tmp_initialValue07`).
- The pattern expansions are verified: for every pattern and scope, nuXmv checks that the
  formula of the core is equivalent, on all traces, to a reference written from the
  definition of the pattern with past-time operators. All 30 pairs of pattern and scope are
  equivalent ([`test/patterns/check-patterns.py`](../test/patterns/check-patterns.py)); for
  example, `never p before r` is `F r => (no p U r)` in the core, and its reference is
  `F r -> G (!(O r) -> !p)`: if r occurs, no p before its first occurrence.
- `RichAndCoreExplicit` and `CoreInitializers` (test-suite) check the rich constructs in both
  models.

## Open points

1. **The modifiers `final`, `finalref` and `finaltarget` are in the core**, and the principle
   asks whether they can be lowered. `finalref` seems to be: the reference of an instance
   keeps its value while the instance exists, e.g., for a reference to integers,
   `[ G (all v : integer | (this.dref = v) => X (some this => this.dref = v)) ]` in `x`.
   `final` and `finaltarget` also forbid new instances or targets, which needs either a
   past-time operator or a quantifier over instances that do not exist yet, so they stay in
   the core until gsdlab/clafer#127, like the `:=` above. To be decided with the semantics.
2. **The clock of `:=` has no syntax of its own.** Under kbak/clafer-semantics#170, a written
   `*` or `0..*` on an abstract clafer makes `:=` a set initializer. The rich explicit model
   leaves the multiplicity of an abstract clafer with a per-instance `:=` out, so that it
   means the same when compiled again; the meaning then depends on a missing token. A keyword
   or annotation would be clearer.
3. **Consumers of the IR and of the explicit model:** the JSON output has the operators of the
   rich constructs and the `_enum` modifier; chocosolver's explicit parser does not read `:=`,
   `=`, patterns or transitions on a declaration, so it reads the core.
4. **The semantics** (kbak/clafer-semantics) defines the core; the rich constructs are
   defined by their lowering, which the semantics may state, e.g., as theorems that each
   pattern's formula meets its definition.
