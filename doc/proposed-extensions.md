# Proposed extensions

Status: Clafer 0.5.7 (Nov 7, 2026). None of the three extensions is implemented, and the grammar
([src/clafer.cf](../src/clafer.cf)) has none of their syntax. Each section below shows how to
write the expression in 0.5.7. Each workaround was checked with `clafer` and `chocosolver`, and
the closure workaround also with `claferIG`.

The extensions were proposed when the queries of the OCL benchmark (B1 and B3) were translated
to Clafer. The translations in plain Clafer are on the wiki (`oclBench/b1`, `oclBench/b3`). The
translations that use the proposed syntax are next to this page:
[b1_ext.page](b1_ext.page) and [b3_ext.page](b3_ext.page).

A fourth proposal, `e instanceOf C`, was dropped: a clafer denotes the set of its instances, so
`e in C` already is the instance-of test, e.g. `[ this.parent in adults ]`.

| Extension | Proposed syntax | 0.5.7 |
|---|---|---|
| Set comprehension | `{p : S \| cond}`, `{p : S \| cond \| e}` | not implemented; a reference clafer with a defining constraint |
| Reverse reference | `a.~r` | not implemented; a quantifier. Both backends have the operator |
| Transitive closure | `a.^r` | not implemented; unrolling, or an Alloy escape. Chocosolver's closure computes one step |

## 1. Set comprehension

Proposed:

```
{p : SetExp | expression-with-p}
{p : SetExp | expression-with-p | set-expression-with-p}
```

The first form denotes the elements of `SetExp` that satisfy the condition, e.g.
`{p : Person | p.age > 15}` for all persons older than 15. The second form also maps each
element, e.g. `{p : Person | p.age > 15 | p.name}` for the names of those persons.

Status: not implemented. A set can only be named by a clafer, so the result is a set-valued
reference clafer, and a top-level constraint states which targets it has:

```clafer
abstract Person
    age -> integer
    husband -> Person ?

// {p : Person | p.age > 15}
older -> Person *
[ all p : Person | p in older.dref <=> p.age > 15 ]

// {p : Person | p.age > 15 | p.husband}
husbandsOfOlder -> Person *
[ all h : Person | h in husbandsOfOlder.dref <=> (some p : Person | p.age > 15 && h in p.husband) ]
```

Notes:

- The constraint must be at the top level, not nested in the reference clafer. In
  `older -> Person *`, `older` has 0..* instances, each pointing to one person. A constraint
  nested in `older` holds for each of these instances, so it holds vacuously when there are none.
- A quantifier on the right of `<=>` needs parentheses.
- When the condition is already a set expression, an equality is enough, e.g.
  `husbands -> Person *` with `[ husbands.dref = Person.husband.dref ]`.
- The scope of the reference clafer must be at least the size of the set.

A comprehension in the language would need its own resolver scope for the bound variable, the
same as a quantifier (see the name resolver specification on the wiki). In Alloy, it would map
to `{p : S | cond}`, and to `{p : S | cond}.e` for the second form. Chocosolver's input has no
set-builder expression, so the generator would introduce an auxiliary set, as the workaround
does.

## 2. Reverse reference

Proposed: `ClaferId.~ClaferId`, a navigation backwards along a reference. In the B3 model,
`ada.~examiner.parent.examinee` gives the examinees of the exams in which `ada` is the examiner.

Status: not implemented. A quantifier over the clafers that hold the reference gives the same
set:

```clafer
// ada.~husband: the persons whose husband is ada
wivesOfAda -> Person *
[ all p : Person | p in wivesOfAda.dref <=> ada in p.husband ]
```

The B3 query becomes:

```
examineeOfAdaAsExaminer -> Person *
[ all p : Person | p in examineeOfAdaAsExaminer.dref <=>
    (some e : Exam | e.examiner = ada && e.examinee = p) ]
```

Notes:

- Where only membership is needed, write the quantifier in the constraint and skip the auxiliary
  clafer, e.g. `[ some e : Exam | e.examiner = ada ]`.
- Both backends already have the operator. In Alloy, a reference `husband` is encoded by
  `r_husband` (parent to reference clafer) and `husband_ref` (reference clafer to target), so
  `ada.~husband` would be `ada.~husband_ref.~r_husband`. Chocosolver has `inverse` in its AST
  and in its JavaScript input: `join(global($ada), inverse(join(relation($husband),
  ref($husband))))` gives the same set as the workaround. Only the syntax and the two
  generators are missing.
- The domain and range restrictions `<:` and `:>` are in the grammar, but navigation paths that
  contain them are not supported yet
  ([gsdlab/clafer#85](https://github.com/gsdlab/clafer/issues/85)).

## 3. Transitive closure

Proposed: `ClaferId.^SubClaferId`, the clafers reachable by following `SubClaferId` one or more
times.

Status: not implemented. There are two workarounds.

When the number of nodes is known, unroll the closure up to paths of that length minus one.
This works with every backend:

```clafer
abstract Node
    succ -> Node *

N1 : Node
    [ succ = N2 ]
N2 : Node
    [ succ = N3 ]
N3 : Node
    [ no succ ]
N4 : Node
    [ succ = N1 ]

// N1.^succ for 4 nodes: paths of length 1 to 3
reach -> Node *
[ reach.dref = N1.succ.dref ++ N1.succ.dref.succ.dref ++ N1.succ.dref.succ.dref.succ.dref ]
```

The only instance has `reach` = `N2`, `N3`.

For the Alloy backend (`claferIG`), an Alloy escape can use `^` directly. A reference `succ` is
encoded by two relations, `r_succ` from the parent to the reference clafer and `succ_ref` from
the reference clafer to its target, so the successor relation is `r_succ.succ_ref`:

```
reach -> Node *
[alloy|
fact { reach.reach_ref = N1.^(r_succ.succ_ref) }
|]
```

`clafer -m alloy` shows the names that the escape must use. The wiki page `graphReachability`
uses this escape to state that one node is reachable from another. Escapes are ignored by
chocosolver.

In the language, `^` would map directly to Alloy. Chocosolver has `transitiveClosure` and
`transitiveReflexiveClosure` in its AST and in its JavaScript input, but on the model above
`join(global($N1), transitiveClosure(join(relation($succ), ref($succ))))` gives only `N2`, and
from `N4` it gives only `N1`: one step instead of the closure. The reflexive closure gives `N1`
and `N2`. The chocosolver tests of the closure (`TransitiveTest`) only check acyclicity and
descendants on small scopes. The closure must be fixed in chocosolver before the language can
map `^` to it; until then, the unrolling is the portable form.
