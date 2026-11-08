# Errata: Clafer: unifying class and feature modeling (2016)

Kacper Bąk, Zinovy Diskin, Michał Antkiewicz, Krzysztof Czarnecki, Andrzej Wąsowski.
*Clafer: unifying class and feature modeling.* Software and Systems Modeling 15(3), 811–845, 2016.
[doi:10.1007/s10270-014-0441-1](https://doi.org/10.1007/s10270-014-0441-1).

This document collects the differences between the paper and the Clafer tools, as of release 0.5.7 (November 2026).
They were found or decided during releases 0.5.3–0.5.7.
Page numbers are the journal's.

Each item has one of these kinds:

- **Correction:** the paper is wrong or inconsistent.
- **Change:** the language deliberately differs from the paper.
- **Clarification:** the paper is silent or ambiguous, and the tools make a choice.
- **Not implemented:** the paper allows something that the tools do not support.
- **Extension:** a language feature that the paper does not cover, listed where it touches the paper's semantics.

The temporal errata are in [temporal-semantics-errata.md](temporal-semantics-errata.md).
Some items concern both papers: S1 and S2 correspond to T10 there, and S3 to the group rule of Definition 3.

## Summary

| # | Kind | Topic | Paper | Since |
|---|---|---|---|---|
| S1 | Change | Children of numeric groups are optional by default | App. 3, p. 840 | 0.3.3, kept in 0.5.4 |
| S2 | Clarification | `opt` makes its children optional (the tools broke it in 0.3.3–0.5.3) | App. 3, p. 840 | 0.5.4 |
| S3 | Clarification | A group counts its own and the inherited children; abstract groups are inheritable bounds | §4.2.1, §6.2.2, App. 3 | 0.3.9 |
| S4 | Clarification | A group counts child instances, and each bag entry counts | §4.2.1, App. 3 | — |
| S5 | Change | A group whose lower bound the children cannot reach is a compile error | App. 3 | 0.5.4 |
| S6 | Change | Abstract clafers may be nested under concrete clafers | §5.3.4, p. 823 | 0.3.9 (Alloy), 0.5.6 (Choco) |
| S7 | Clarification | `parent` at the top level: the synthetic root, and top-level abstract clafers | §5.3.4, p. 823; App. 4 | 0.5.3, 0.5.7 |
| S8 | Clarification | Implicit `.dref` | App. 4, p. 840 | 0.5.3 for unions |
| S9 | Correction, clarification | Name resolution: Ancestors before Targets, and the rules beyond the paper's | App. 4, pp. 840–841 | 0.5.3, 0.5.6 |
| S10 | Not implemented | Inheritance from concrete clafers | §5.5, p. 825 | — |
| S11 | Extension | Primitive types and arithmetic | App. 4, pp. 841–842 | 0.5.5 |
| S12 | Extension | Assertions | — | 0.5.6 |
| K1–K5 | Correction | The formal corrections in clafer-semantics | §5.3.4, §6, Table 3, Fig. 21, Fig. 23, App. 2 | — |

## S1. Children of numeric groups are optional by default (change)

**Paper (Appendix 3, p. 840):** "By default, clafers have multiplicity 1..1." The keywords `xor`, `or`, `opt` and `mux` "make children optional by default". So a child of a numeric group, such as `2..3`, is mandatory by default.

**Tools:** a child without a multiplicity is mandatory only under no group or under `0..*`.
Under a keyword group or any other range, it is optional (`0..1`):

```
2..3 Colours
  red        // 0..1
  green      // 0..1
  blue       // 0..1
```

**Why:** with mandatory children, a numeric group is useless or contradictory.
`2..3` over three mandatory children always counts 3, so the group says nothing.
`1..2` over three mandatory children makes the model unsatisfiable.
The only way out would be a `?` on every child.

**History:** the paper's rule was the compiler's rule until 2013. Commit `65a23bb` (clafer 0.3.3) replaced it with an interval rule: a child is mandatory under `0..*` and optional under any other group.
The maintainers confirmed the numeric part of that rule as a deliberate change on 2026-10-25 ([clafer 0.5.4](https://github.com/gsdlab/clafer/pull/101)).
clafer-semantics adopted the same policy as language evolution, not as a paper correction ([kbak/clafer-semantics#118](https://github.com/kbak/clafer-semantics/issues/118), [#119](https://github.com/kbak/clafer-semantics/pull/119)).

## S2. `opt` makes its children optional (clarification)

**Paper (Appendix 3, p. 840):** `opt` denotes `0..*` and makes the children optional by default, like the other keywords.

**Tools:** this agrees with the paper again since 0.5.4.
The interval rule of S1 broke it from 0.3.3 to 0.5.3: `opt`, being `0..*` like no group at all, made its children mandatory, so `opt` had no effect.
Since 0.5.4, only the keywords set `_isKeyword` in the IR, and a child of `opt`, including an inherited `opt`, is optional.

**Note:** `opt` is not `0..1`; that is `mux`.
The temporal paper (Juodisius et al., §6.1) states the interval rule and omits `opt`; see T10 in the temporal errata.

## S3. Groups and inheritance (clarification)

**Paper:** a group cardinality constrains the number of child instances of its clafer (§4.2.1, p. 817; §6.2.2, p. 829).
Appendix 3 (p. 840) says that no explicit group cardinality stands for `0..*`, "except when it is inherited from clafers supertype".
It does not say which children an inherited group counts.
Definition 3, item 6, of the temporal paper applies the group of every clafer that types an instance, each over that clafer's own children.

**Tools:** since February 2015 (commit `3ce5252`), a group is enforced only for concrete clafers, over the union of their own and their inherited children.
The group of an abstract clafer is a bound that its subclafers inherit or redefine, not an invariant over the abstract clafer's own children:

```
abstract xor A
  x ?
  y ?
B : A
  z ?
```

An instance of `B` with only `z` is valid: `B`'s inherited `xor` counts `x`, `y` and `z`.
Under Definition 3 of the temporal paper, `A`'s `xor` over `x` and `y` would also apply, and that instance would be invalid.
A subclafer can refine the inherited group, e.g. `abstract xor RelayPort : Port` under `abstract or Port` (test `groupCardInheritance.cfr`).

Relative to Definition 3, item 6 of the temporal paper, this is a change of meaning, not a typo (T11 in the [temporal errata](temporal-semantics-errata.md)).
clafer-semantics formalizes the same rule (its decision D6, [group compilation](https://github.com/kbak/clafer-semantics/blob/main/docs/group-compilation.md)).
Models written before 2015 may depend on the old behaviour, e.g. ClaferMooVisualizer's `ClaferMooVizPaperExample*`.

## S4. A group counts child instances (clarification)

**Paper:** "xor on size … states that only one child instance of either small or large is allowed" (Appendix 3, p. 840).

**Tools:** the count is the number of child instances, not the number of child clafers present.
A child with multiplicity `1..5` under `2..3` can satisfy the group alone, with two or three instances (test `group_cardinality_counts_child_instances.cfr`).
Each instance of a bag reference (`->>`) is a child instance of its own, so two entries pointing to the same target count twice.

clafer-semantics counts the same way: distinct child head objects, with distinct bag heads counted separately.

## S5. Unreachable group lower bounds are compile errors (change)

**Paper:** a group whose lower bound the children cannot reach, e.g. `xor` over no children, makes every instance of its clafer invalid.
The model is then satisfiable only when the clafer has no instances.

**Tools (0.5.3):** such a group was skipped in the Alloy and Choco output, so `Phone / xor Mode` with no children under `Mode` gave instances with `Mode`.

**Tools (0.5.4):** it is a compile error, decided by the maintainers on 2026-10-24.
Examples are `xor` or `or` over no children, and `3..*` over two optional children.
The children include the inherited ones, and the group may be inherited or redefined.
An abstract clafer's group is not checked, since its subclafers may add children.

clafer-semantics keeps the paper's meaning (the context must be empty) and treats the compiler's rejection as a separate check.

## S6. Abstract clafers nested under concrete clafers (change)

**Paper (§5.3.4, p. 823):** when a top-level clafer is abstract, all its descendants are abstract by default; "this is the only case in which abstract clafers are nested."

**Tools:** an abstract clafer may also be nested under a concrete clafer:

```
System
  abstract Port
    speed -> integer
  p1 : Port
  p2 : Port
```

The concrete clafer is the parent of the instances of the abstract clafer's subclafers.
A clafer that extends a nested abstract clafer must have the same parent, as in §5.5, or be nested in a clafer that extends that parent (`extends_nested_abstract_in_context.cfr`).
The Alloy backend supports it since 0.3.9.
The Choco backend supports abstract clafers nested in abstract clafers since 0.4.3, and nested in concrete clafers since 0.5.6 ([gsdlab/chocosolver#23](https://github.com/gsdlab/chocosolver/issues/23)), with the same instances as claferIG.

## S7. `parent` at the top level (clarification)

**Paper (§5.3.4, p. 823):** the synthetic root `Sing`, a singleton class, "is the parent of top-level concrete clafers", and top-level constraints are in its context (Appendix 4).
A top-level abstract clafer has no parent in the containment hierarchy.
So `parent` is undefined in the context of such a clafer, e.g. in a constraint of `abstract Component`.
The paper does not say what `parent` of a top-level concrete clafer denotes in a constraint, nor what the reserved name `root` denotes; by the containment hierarchy, it is the root.

**Tools, top-level concrete clafers (0.5.7, [gsdlab/clafer#112](https://github.com/gsdlab/clafer/issues/112)):** `parent` of an instance of a top-level concrete clafer is the root, as in the paper.
The root has no atom in the static outputs (Alloy, Choco): a navigation from it is a navigation from the top level, so in a top-level clafer `b`, `parent.a` is `root.a`, i.e. `a`.
As the paper's singleton, `some root`, `one root` and `lone root` hold, `no root` does not, and `#root` is 1.
Other uses of `root` as a set, e.g. a union or a variable ranging over it, are refused, since the outputs have no atom for it; a comparison of `root` with a clafer is a type error, and `root = root` is redundant.
The parent of a set of instances, e.g. `a.parent` for `a ?`, is the relational join: the root when an instance exists, and empty otherwise. So `some a.parent` is `some a`, `#a.parent` is 1 or 0, and `a.parent.c` is `c` when `a` exists.
The temporal output has a root signature, and translates `parent` with the parent relations as before.
Up to 0.5.6, `parent` of a top-level concrete clafer compiled to Alloy that refers to a missing relation (`this.~@r_c0_b`) and failed in chocosolver ("Cannot join c0_b . parent"); `[ some root ]` compiled to an undefined `root`.

**Tools, top-level abstract clafers (0.5.3, [gsdlab/clafer#84](https://github.com/gsdlab/clafer/issues/84)):** `parent` of an instance of a top-level abstract clafer is its actual parent, i.e. the parent of the concrete subclafer that it is an instance of.
In the Alloy output, it is the union of the parent relations of the subclafers, and the Choco backend does the same.
For a subclafer at the top level, the actual parent is the root, which neither output had up to 0.5.6: in Alloy, the instances of the top-level subclafers had no parent, so `abstract Feat [ some parent ]` with `f1 : Feat` at the top level and `f2 : Feat` in `g` had no instances, and chocosolver refused the model.
Since 0.5.7 (#112), a constraint of such a clafer on the parent of `this` is split on `this`: for the instances of the top-level subclafers, the parent is the root, and for those of each nested subclafer, its parent.
When all the subclafers are at the top level, the parent is the root.
The parent of a variable of a clafer with subclafers at both levels, e.g. `all v : Feat | some v.parent`, is refused, since it is not decided per instance (`test/negative/parent_of_mixed_abstract_variable.cfr`).

## S8. Implicit `.dref` (clarification)

**Paper (Appendix 4, p. 840):** the constraint language differs from Alloy's mainly in its name resolution and in the default `some` quantifier.
It does not describe the implicit dereferencing of reference clafers.

**Tools:** where a value is expected, a reference clafer stands for its target: `[ speed = 3 ]` is `[ speed.dref = 3 ]`.
Since 0.5.3, this also applies to the operands of a union (`BobPicks ++ 3`, `others ++ p1`), and `sum` and `product` over a union are split into a sum over each operand.
Since 0.5.7 ([gsdlab/clafer#87](https://github.com/gsdlab/clafer/issues/87)), a comparison (`=`, `!=`, `in`, `not in`) of two navigations to reference clafers compares their targets: `this.a = parent.b.a` is `this.a.dref = parent.b.a.dref`. Both readings type check, and the tools took the first, which compared the instances of `a`; those of different parents are never the same. An operand that is `this`, a variable or ends with `dref` is compared as written, which keeps the comparisons of instances, e.g., `this in b.a` in `sel -> b.a`.

## S9. Name resolution: Ancestors before Targets (correction), and beyond the paper's rules (clarification)

The paper's rules (Appendix 4, pp. 840–841) cover names in constraints: 1. Reserved names, 2. Binding, 3. Descendants, 4. Targets ("Similar to the previous step but additionally take into account clafers reachable via references"), 5. Ancestors (for each ancestor, Descendants and, if necessary, Targets), 6. Top level, 7. Error.

**The paper is silent on** what "reachable via references" includes: the target of the context clafer's own reference, or the targets of its descendants' references, and whether it follows references of references.
The tools search only the context clafer's own target, not the targets of its descendants' references, and they follow a chain of references: in `r -> b` with `b -> c` and `c` having `speed`, `[ speed > 0 ]` in `r` is `this.dref.dref.speed`.

**The order of Targets and Ancestors (corrected to the tools' order, decided on 2026-11-04):** the tools look up a name among the children of the context's target only after the ancestors: Descendants, Ancestors, target children, Top level (clafer 0.5.3, `resolveName` in `ResolverName.hs`). Before 0.5.3, they did not look among the target's children at all. Example:

```
abstract Port
    speed -> integer
abstract Component
    abstract port : Port *
    abstract link -> Port *
        latency -> integer
        [ latency <= speed ]
```

By the paper's order, `speed` is the speed of the linked port, `this.dref.speed` (Targets). In the tools, it is the speed of the component's own ports, `this.parent.port.speed` (Ancestors), since the component has a `port` with a `speed`. Without a `port` in `Component`, the tools find the target's `speed`.

Both readings have uses, and models rely on the tools' order: in `test/positive/personRelatives.cfr` and `paths.cfr`, `childs -> Person *` has `[ this.age < age ]`, meaning that a child is younger than its parent, where `age` is the parent's (Ancestors). By the paper's order, `age` would be the child's, and the constraint would read `child.age < child.age`. With the paper's order (checked 2026-11-03 by swapping the two rules), only these two models of the test suite change.

The paper's order is corrected to the tools' order ([kbak/clafer-semantics#121](https://github.com/kbak/clafer-semantics/issues/121)): the target's children come after the ancestors, and a model writes `this.speed`, which resolves through the reference, to get the target's. The formal semantics works on resolved names, so the decision does not change it; the Lean compiler adopted the same order ([kbak/clafer-compiler-lean#68](https://github.com/kbak/clafer-compiler-lean/pull/68)), checked against the Haskell compiler on `personRelatives.cfr`'s case, target fallback and a chain of two references. Writing `this.` or `parent.` makes the choice explicit.

The tools also choose:

- **Inside a reference clafer (0.5.3):** an ancestor name, such as `Machine` or `parent`, is the enclosing instance, and, when no ancestor has the name, the children of the target resolve through the reference, as above.
- **Navigation from `this`:** `this.speed` in a reference clafer resolves through the reference to the target's `speed`.
- **Navigation after `dref` (0.5.7, [gsdlab/clafer#108](https://github.com/gsdlab/clafer/issues/108)):** the names after an explicit `dref` are the children of the reference's target, the one that the clafer declares or the nearest that it inherits: `this.dref.speed` is the target's `speed`, also when the reference clafer has a child `speed` of its own. Before, the name was looked up in the reference clafer again and resolved through the reference a second time, `this.dref.dref.speed`, which did not compile (or reported an ambiguous name when the target was a reference too). For a reference to a union of clafers, the name is looked up through the reference, without a second `dref`.
- **The reserved name `root`:** the paper's reserved names are "such as `parent`, `dref`, and `this`" (rule 1). The tools also reserve `root` ([gsdlab/clafer#57](https://github.com/gsdlab/clafer/issues/57), 2016), the synthetic root, e.g. `root.b` for a top-level `b` that a nested `b` hides (S7).
- **Super clafers (0.5.3, [gsdlab/clafer#86](https://github.com/gsdlab/clafer/issues/86)):** a super clafer's name is resolved to the nearest abstract clafer of that name that the parent inherits, excluding the clafer itself, which used to resolve as its own super.
- **Partially qualified names (0.5.6):** a qualified name (`normal::yellow`) matches whole clafer names only. `yellow` matched `yellow_on` too, so it was ambiguous.

## S10. Inheritance from concrete clafers (not implemented)

**Paper (§5.5, p. 825):** "Inheritance among any types of clafers is allowed", subject to three restrictions. The temporal paper (Definition 1, item 5) also allows a concrete clafer to extend a concrete clafer.

**Tools:** a super clafer must be abstract. `B : A` with a concrete `A` gives `No superclafer found: A`.
This is [gsdlab/clafer#82](https://github.com/gsdlab/clafer/issues/82), which wants it for example-driven modelling.

## S11. Primitive types and arithmetic (extension)

**Paper (Appendix 4, pp. 841–842):** the primitive domains are `int` and `string`, the arithmetic is `+` and `-`, and integers are unbounded.

**Tools:**

- **Types:** `integer` (`int`), `string`, `decimal` (0.5.5), `double` and `real`. Integers are decimals, and decimals and doubles are reals. A decimal and a double do not mix, because most decimals are not doubles.
- **Decimals:** they have a fixed number of fractional digits, the model's scale: the most fractional digits of its literals as written, or `--decimal-digits`. `decimal * decimal` and divisions with a decimal round half away from zero, and a division of integers stays an integer division. Only the Choco backend supports decimals.
- **Unsupported types:** no backend supports `double` or `real`.
- **Arithmetic:** also `*`, `/`, `%`, `sum`, `product`, `min`, `max` and `#`. The operands of `+` and `-` need not have the same type, unlike the paper's rule `Exp1 :: τ, Exp2 :: τ`: an integer and a decimal give a decimal.
- **Bounded integers:** the backends bound integers. Alloy uses a bit width, and its integers wrap around. Choco uses the range `--minint`..`--maxint` (0.5.3, also in `//# OPTIONS`).

## S12. Assertions (extension)

The paper does not have assertions.
In the tools, `assert [ … ]` is a constraint that must hold in every instance.
claferIG checks it within the scopes with `check`, and a failure gives a counterexample.
Since 0.5.6, an assertion can be nested, and then holds for each instance of its clafer.
Nested assertions used to be ignored.

## Differences of the tools from the paper

None is open: the last one, the order of Targets and Ancestors in name resolution (S9), was decided for the tools' order on 2026-11-04 ([kbak/clafer-semantics#121](https://github.com/kbak/clafer-semantics/issues/121)).

Compiler bugs that do not concern the paper's semantics are tracked as issues instead, e.g., `this.dref.speed` was a compile error ("Cannot deref from type") from at least 0.5.2 to 0.5.6 ([gsdlab/clafer#108](https://github.com/gsdlab/clafer/issues/108), fixed in 0.5.7, S9), and `parent` of a top-level clafer gave outputs that do not run ([gsdlab/clafer#112](https://github.com/gsdlab/clafer/issues/112), fixed in 0.5.7, S7). Also [gsdlab/clafer#109](https://github.com/gsdlab/clafer/issues/109) (`final` on a clafer that inherits its reference, fixed in 0.5.7, T8 of the temporal errata) and [gsdlab/claferIG#46](https://github.com/gsdlab/claferIG/issues/46) (unsat cores without the constraints of clafers in abstract clafers).

## K1–K5. Corrections already in clafer-semantics

Kacper Bąk's Lean formalization keeps a reading companion to the paper with corrections and clarifications: [clafer-semantics/docs/sosym-errata.md](https://github.com/kbak/clafer-semantics/blob/main/docs/sosym-errata.md).
It cites the pages of the 37-page e-offprint, so its page numbers differ from the journal's.
These are its corrections, in short:

- **K1. Disjointness (Table 3; §6.1.2 and Fig. 21):** disjointness applies to maps into a common target, whose images must be disjoint. Table 3's common-source shape and its source-inequality condition are wrong.
- **K2. Top-level abstract clafers (§5.3.4; §6.2.3, Fig. 23; Table 7):** a top-level abstract clafer keeps its head class. What it lacks is the source class and the parent-dependent maps. §5.3.4 says it excludes the head class, which contradicts §6.2.3 and Fig. 23.
- **K3. The version constraint (Fig. 21a; §6.1; Fig. 8 and §4.2.3; Appendix 6):** the intended condition is `display.version ≥ server.version`. In Fig. 21a, where `server` is partial, it is guarded by the presence of a server; Appendix 6 has a mandatory `server → ECU` and the unguarded `[ version ≥ server.version ]`, which is correct there. The prose of §6.1 reverses the inequality.
- **K4. Multiplicities in Fig. 23 (Fig. 23; Table 8):** seven associations need the source multiplicity `0..1` instead of `1`: `head_map`, `parent_map`, `dref_map`, `target_map`, `super_s`, `super_h` and `super_t`. Otherwise every map role would need both the label `parent` and the label `dref`.
- **K5. Span composition (Appendix 2):** composing spans agrees with relational composition only after forgetting link identity. Two paths through different intermediate objects give two composite links but one related pair.

The same document has nine clarifications: the disjointness of incomparable declaration heads, links and bag keys, complete formula bindings, metamodel representation, role-presence guards, gluing by resolved identity, the intersection glyph in Appendix 4, the group and inheritance rules of S3, and inherited fields of abstract types.

## The Lean formalization

The formalization was completed in November 2026, and it found no further issues with the paper or the tools.
It has two parts:

- **[clafer-semantics](https://github.com/kbak/clafer-semantics)** defines the meaning of Clafer independently of any compiler, with the corrections K1–K5 and the decisions of these errata, and proves its properties in Lean 4. Its [key proved properties](https://github.com/kbak/clafer-semantics/blob/main/docs/proved-properties.md) include, for structural Clafer: the paper's Compile produces a valid model of Clafer Shapes (§6), gluing by resolved identity preserves the declarations, the source constraints of a selected fragment agree with the compiled and glued model, and a finite candidate checker decides structural satisfaction exactly (inheritance, root, parent and reference conditions, multiplicities, groups as in S3 and S4, disjointness as in K1). The telematics model of Appendix 6 is proved to have a satisfying interpretation.
- **[clafer-compiler-lean](https://github.com/kbak/clafer-compiler-lean)** is a second Clafer-to-Alloy compiler, proved against that semantics. Every Alloy instance that it gets back decodes to a valid Clafer configuration, and every configuration that fits the scopes and the bit width has an Alloy instance; undefined values, such as an integer taken from an empty reference, stay undefined. Its [lessons](https://github.com/kbak/clafer-compiler-lean/blob/main/docs/lessons.md) state these guarantees and where they end.

**What it does not cover:** the Clafer tools themselves. The Haskell compiler, chocosolver and claferIG are not proved; they agree with the formalization on the cases compared, within the language that both compilers accept, which is smaller than the tools'. Parsing, the Alloy Analyzer and the SAT solvers are outside the proofs, and a bounded search proves nothing beyond its scopes.

## Sources

- clafer's [CHANGES.md](../CHANGES.md), versions 0.5.3–0.5.7, and chocosolver's [CHANGES.md](https://github.com/gsdlab/chocosolver/blob/master/CHANGES.md).
- clafer's [CheatSheet](CheatSheet.md), which describes the current rules.
- clafer-semantics: [proved-properties.md](https://github.com/kbak/clafer-semantics/blob/main/docs/proved-properties.md), [sosym-errata.md](https://github.com/kbak/clafer-semantics/blob/main/docs/sosym-errata.md), [sources.md](https://github.com/kbak/clafer-semantics/blob/main/docs/sources.md) (current child-default policy), [group-compilation.md](https://github.com/kbak/clafer-semantics/blob/main/docs/group-compilation.md), [resolved-ir-comparison.md](https://github.com/kbak/clafer-semantics/blob/main/docs/resolved-ir-comparison.md) (decisions D1–D8), and [kbak/clafer-semantics#115](https://github.com/kbak/clafer-semantics/issues/115), the report of the fixes in 0.5.4.
- clafer-compiler-lean: [lessons.md](https://github.com/kbak/clafer-compiler-lean/blob/main/docs/lessons.md), and [kbak/clafer-compiler-lean#68](https://github.com/kbak/clafer-compiler-lean/pull/68) (S9).
- clafer commits `cf9921b` (2011, keyword-based child defaults), `65a23bb` (2013, the interval rule), `3ce5252` (2015, groups count inherited children).
