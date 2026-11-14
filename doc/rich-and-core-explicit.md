# The rich and the core explicit model

Status: experiment, on the branch `experiment/explicit-initializers`; not in a release.

An explicit model is a Clafer model that the compiler does not transform any further:
compiled again, it prints itself. Up to Clafer 0.5.8 there is one explicit model,
`clafer -m clafer`, and everything that is not a default is desugared before it: enumerations
become clafers, initializers become constraints, and behavioral patterns and transitions
become LTL formulas. The explicit model then shows what the backends solve, but the
modeling intent is lost, and the model is hard to read and hard to map back to what was
written: for example, `never p between q and r` is
`G (((q && no r) && F r) => (no p U r))`.

This redesign keeps two explicit models, both fixpoints:

| | `clafer -m clafer` | `clafer -m clafer --core` |
|---|---|---|
| name | rich explicit model | explicit core model |
| keeps | enumerations, initializers, behavioral patterns, transitions | the core language only |
| for | reading, editing, storing, diffing; backends that use the intent | checking what the backends solve |
| IR | the IR as resolved, also the JSON output (`-m json`) | the IR after `lowerToCore` |

The syntactic sugar that remains is defaults only: the keyword multiplicities (`?`, `*`, `+`)
and group cardinalities (`xor`, `or`, `mux`, `opt`), the completion of paths (`x` is
`this.x` or `parent.x`), the automatic `dref`, `: integer` for `-> integer`, `-> 1` for
`-> integer = 1`, and the keywords `eventually`, `globally`, `next`, `until` and
`weakuntil` for `F`, `G`, `X`, `U` and `W`. Each has a single obvious expansion, so the rich
explicit model loses no intent by writing it out.

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
`Language.Clafer.Intermediate.Core` (and `Initializers` for the initializers). A backend
that can use the intent, such as a future SMV backend or a state machine view, may read the
rich IR instead; it must then agree with the lowering, which can be checked by comparing the
instances, traces and counterexamples of the two levels.

Both levels are checked on the test models: each rich and each core explicit model compiles
to itself, and the core of each model is the explicit model that Clafer 0.5.8, which
desugared everything, prints for it, except for a `:=` whose value has temporal operators
(open point 2).

## The rich constructs

### Enumerations

`enum Color = red | green` is an abstract clafer with a concrete clafer `1..1` for each
literal, as before, now marked as an enumeration (`_enum` in the modifiers of the IR). The
rich explicit model prints the enumeration; the core prints the clafers:

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
  `[ initially (some xs => xs.dref = e) ]` in the parent.

See [initial-value.md](initial-value.md) for the meaning.

### Behavioral patterns

The patterns of Dwyer et al. (Patterns in Property Specifications for Finite-State
Verification, ICSE 1999), `never`, `sometime`, `lonce`, `always`, `s must precede p` and
`s must follow p`, in the scopes globally, `before r`, `after q`, `between q and r` and
`after q until r`, are operators of the IR, e.g., `never between` with the arguments
`p`, `q`, `r`. The core is their LTL formula.

The expansions are verified: for every pattern and scope, a nuXmv model checks that the
formula of the core is equivalent, on all traces, to a reference written from the
definition of the pattern with past-time operators. All 30 pairs of pattern and scope are
equivalent; for example, `never p before r` is `F r => (no p U r)` in the core, and its
reference is `F r -> G (!(O r) -> !p)`: if r occurs, no p before its first occurrence.

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

## Open points

1. **The clock of `:=` has no syntax of its own.** Under #170, a written `*` or `0..*` on an
   abstract clafer makes `:=` a set initializer. The rich explicit model leaves the
   multiplicity of an abstract clafer with a per-instance `:=` out, so that it means the same
   when compiled again; the meaning then depends on a missing token. A keyword or annotation
   would be clearer.
2. **A `:=` whose value has temporal operators stays in the core.** The value is evaluated in
   the context of the parent (gsdlab/clafer#123), which the core language cannot write in the
   context of `x` without past-time operators; the temporal Alloy generator interprets it.
3. **Consumers of the IR and of the explicit model need updating:** the JSON output has new
   operators and the `_enum` modifier; chocosolver's explicit parser does not read `:=`,
   `=`, patterns or transitions on a declaration, so it needs the core.
4. **The semantics** (kbak/clafer-semantics) defines the core; the rich constructs are
   defined by their lowering, which the semantics may state, e.g., as theorems that each
   pattern's formula meets its definition.
