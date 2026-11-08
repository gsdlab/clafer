# The root

Status: analysis of Clafer 0.5.7 (Nov 7, 2026). It records how the outputs represent the root,
and why the static and the temporal outputs differ. The rules for `parent` and `root` are in
[errata S7](static-semantics-errata.md#s7-parent-at-the-top-level-clarification).

## The paper

The paper (§5.3.4, p. 823) has a synthetic root `Sing`, a singleton class that "is the parent of
top-level concrete clafers". Top-level constraints are in its context (Appendix 4). The paper
does not say what `parent` of a top-level clafer denotes, nor what the reserved name `root`
denotes; by the containment hierarchy, both are the root (errata S7). The tools reserve `root`
since [gsdlab/clafer#57](https://github.com/gsdlab/clafer/issues/57), e.g. `root.b` for a
top-level `b` that a nested `b` hides (`test/positive/gi57-root-keyword.cfr`).

Both kinds of outputs follow the paper. They differ in whether the root is written out.

## Static models: a root without an atom

In the static outputs (`-m alloy`, `-m choco`), the root has no instance that a constraint can
refer to. `ResolverRoot` resolves the uses of `root` and of `parent` at the top level before the
outputs are generated ([gsdlab/clafer#112](https://github.com/gsdlab/clafer/issues/112), 0.5.7):

- A navigation from the root is a navigation from the top level: `root.a` is `a`, and in a
  top-level clafer `b`, `parent.a` is `a`.
- The root as a value is a constant: `some root`, `one root` and `lone root` hold, `no root` does
  not, and `#root` is 1.
- The parent of a set of instances of top-level clafers is the root when the set is not empty:
  `some a.parent` is `some a`, and `#a.parent` is 1 or 0.
- A constraint of a top-level abstract clafer on the parent of `this` is split on `this` when
  some of its subclafers are at the top level and some are nested: for the instances of the
  top-level subclafers, the parent is the root.
- Other uses of `root` as a value are refused, e.g. `[ some (root ++ a) ]` gives "The root has no
  instance". So are the following uses: a variable that ranges over the root, `root` as a child,
  a comparison of `root` with a clafer, which is a type error, and the parent of an optional
  top-level clafer as a set. The parent of a variable of an abstract clafer with subclafers at
  both levels is refused too.

The accepted uses are tested in `test/positive/parent_of_top_level.cfr` and
`test/positive/gi84-parent-top-level-abstract.cfr`. The refused ones are tested in
`test/negative`:

| Model | Constraint | Error |
|---|---|---|
| `root_in_union.cfr` | `some (root ++ a)` | The root has no instance |
| `variable_over_root.cfr` | `all r : root \| some r.a` | A variable cannot range over the root |
| `root_as_child.cfr` | `some root.root` | The root is not a child of any clafer |
| `compare_root_with_clafer.cfr` | `root = a` | type error |
| `parent_of_optional_top_level.cfr` | `extra.parent = extra.parent` for `extra ?` | The parent of extra is the root when an instance exists |
| `parent_of_mixed_abstract_variable.cfr` | `all v : Feat \| some v.parent` | The parent of an instance of Feat is the root for its top-level subclafers |

The negative tests only check that a model is refused, not the message.

How each output represents the root:

- **Alloy:** the output has no root signature. The top-level clafers are signatures without a
  parent relation.
- **Choco:** chocosolver has a root internally. `AstModel` defines a clafer `root` with
  cardinality 1..1, the parent of the top-level concrete clafers, and `AstCompiler` gives it the
  constant set `{0}`. Its JavaScript input has no expression for it, so the generated model
  cannot refer to it.

So the static outputs leave the root out because of how the generators and chocosolver's input
language were designed. The solvers could represent it.

## Temporal models: an explicit root

The temporal output (`-m alloyLtl`, Alloy 6) writes the root out, as the paper's singleton:

```alloy
one sig root
{ var r_a : set a }
fact { always (lone root.@r_a) }

sig a
{ p_a : lone root }
fun alive_a : set a { root.@r_a }
fact { always ~@r_a in @p_a }
```

(`test/regression/tmp_Global00.als.reg`, for a top-level `a ?`.) A top-level clafer belongs to the root as a nested clafer belongs to its parent, and its
instances exist in a state when the root holds them. Errata S7 notes that "the temporal output
has a root signature, and translates `parent` with the parent relations as before".
`ResolverRoot` does not apply to temporal models, so the uses of `root` that static models refuse,
e.g. `root ++ a`, are accepted there.

Several rules of the temporal semantics rely on every clafer, top-level ones included, having
a parent relation:

- the lifetimes of the instances, which may reappear
  ([temporal errata T1](temporal-semantics-errata.md#t1-instances-may-reappear-change));
- temporal obligations end with the parent of the context instance, and top-level constraints,
  whose context is the root, keep plain LTL
  ([T2](temporal-semantics-errata.md#t2-temporal-obligations-end-with-the-parent-of-the-context-instance-change),
  `test/positive/tmp_obligation_outlives_instance.cfr`, `tmp_negated_obligations.cfr`);
- `final`, `finalref` and `finaltarget` hold while the parent instance exists, and a `final`
  clafer whose ancestors are all `final` gets a static relation
  ([T8](temporal-semantics-errata.md#t8-final-clarification));
- a top-level constraint holds in every state with `this` bound to the root
  ([T9](temporal-semantics-errata.md#t9-constraints-and-patterns-hold-in-every-state-clarification));
- `parent` of a top-level instance is the root, through `p_a`
  (`test/positive/tmp_parent_across_lifetimes.cfr`).

## Option 1: a synthetic root in temporal models

That is, the temporal output would leave the root out, as the static outputs do.

**Benefits:**

- The same uses of `root` would be accepted in static and temporal models. Today `root ++ a` is
  refused in a static model and accepted in a temporal one; this is the only difference that a
  modeler can see.
- `ResolverRoot` would apply to all models, instead of only static ones.
- The Alloy model would be slightly smaller: one atom fewer, and no parent relation for the
  top-level clafers. The root is one fixed atom, so solving would barely get faster.

**Costs:**

- The top-level clafers would need another way to appear and disappear, e.g. variable
  signatures, beside the parent relations of the nested clafers: two encodings of lifetimes
  instead of one.
- Each rule listed above would need a case for the top level, and would have to be validated
  again on all the temporal test models, the regressions and the explicit-form fixpoints, and
  claferIG's model tests.
- claferIG and the web tools read the traces, which include the root atom.

## Option 2: an explicit root in static models

That is, the static outputs would write the root out, as the temporal output does.

**Benefits:**

- `root` would be a value like any other, with the same meaning in all outputs and in the paper.
  The refused uses would be accepted, and errata S7 would be shorter.
- Most of `ResolverRoot` would go: the constants for `some root` and `#root`, the rewriting of
  `some a.parent`, and the splitting of the constraints of top-level abstract clafers. `parent`
  would be a join at every level, as in the temporal output.
- The solvers would barely be affected. Alloy would get one atom and one relation per top-level
  clafer. Choco already has the root, with its constant set.

**Costs:**

- Every static output changes: all Alloy and Choco regressions, the explicit-form fixpoints and
  the instance counts would have to be checked again.
- claferIG, ClaferIDE and ClaferMooVisualizer would show a root in each instance, unless each of
  them hides it.
- chocosolver's JavaScript input would need an expression for the root, and possibly parent
  links for the top-level clafers: a change of its public input language, with a new version that
  clafer must require.
- Modelers would gain little. The root is a constant singleton, so the refused uses have hardly
  any modeling purpose: `root ++ a` mixes the root with clafers, and a variable over `root`
  binds one fixed value. The meaningful uses already work: `root.a`, `parent` at the top level,
  and `some root`, `one root` and `#root`.

## Decision

Neither option for 0.5.7. Both outputs implement the paper's singleton root: the temporal output
writes it out, since its lifetimes rely on the parent relations, and the static outputs leave it
out, since it never changes there. They agree on every use of `root` that a static model
accepts.

The only difference, the uses that static models refuse, can be closed without changing either
encoding:

- apply the checks of `ResolverRoot` on the uses of `root` to temporal models as well, without
  its rewriting; or
- state in errata S7 that temporal models accept these uses.

An explicit root in static models fits best in a release that changes chocosolver's input
language anyway. Even then, it would mainly simplify the compiler; modelers would gain little.
