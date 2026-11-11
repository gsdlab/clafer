# Errata: Clafer: Lightweight Modeling of Structure, Behaviour, and Variability (2019)

Paulius Juodisius, Atrisha Sarkar, Raghava Rao Mukkamala, Michał Antkiewicz, Krzysztof Czarnecki, Andrzej Wąsowski.
*Clafer: Lightweight Modeling of Structure, Behaviour, and Variability.* The Art, Science, and Engineering of Programming 3(1), article 2, 2019.
[doi:10.22152/programming-journal.org/2019/3/2](https://doi.org/10.22152/programming-journal.org/2019/3/2), [arXiv:1807.08576](https://arxiv.org/abs/1807.08576).

The paper formalized behavioural Clafer, but its semantics was never implemented: Clafer 0.5.0 only had an experimental Alloy 4.2 generator (§6.2).
Clafer 0.5.6 (November 2026) is the first implementation. It compiles temporal models to the temporal logic of Alloy 6, and claferIG 0.5.6 generates and checks their traces.
Implementing the paper required the changes below, which were decided on 2026-10-28 and 2026-10-29 (T1–T4, T8), with T2 revised on 2026-11-03 and extended to negated obligations on 2026-11-04 ([gsdlab/clafer#110](https://github.com/gsdlab/clafer/issues/110)). Items T1, T3, T11 and T13 were corrected on 2026-11-04 after a review against the implementation ([gsdlab/clafer#111](https://github.com/gsdlab/clafer/issues/111)). The corrections were found while implementing and testing the semantics, and while checking the paper's examples for this document.
Pages are the article's (`2:n`).

The corrected semantics is formalized in Lean 4 in [clafer-semantics](https://github.com/kbak/clafer-semantics), completed in November 2026, with no further issues found (see [Formalization](#formalization)). The items below name what is proved about them.

The kinds of items are as in the [static errata](static-semantics-errata.md): **Correction**, **Change**, **Clarification**, **Extension**.

## Summary

| # | Kind | Topic | Paper |
|---|---|---|---|
| T1 | Change | Instances may reappear | Def. 5, item 2, p. 2:28 |
| T2 | Change | Temporal obligations end with the parent of the context instance, also when negated (0.5.6 has a bug) | §6.1, pp. 2:30–2:31; §4.2, p. 2:17 |
| T3 | Extension | Transitions of clafers | §6.1, p. 2:29 |
| T4 | Change | A chain of transitions is a sequence | §4.5, p. 2:22; §6.1, p. 2:31 |
| T5 | Correction | Assertions hold for all traces; possible scenarios are constraints | §4.5, pp. 2:21–2:22; §6.1, pp. 2:29–2:30 |
| T6 | Correction | The negative scenarios and the model-checking recipe of §4.5 | §4.5, p. 2:22 |
| T7 | Correction | `initially` holds in the first state of each lifetime | §6.1, p. 2:31; §4.1, p. 2:13 |
| T8 | Clarification | `final` | §6.1, p. 2:32; §4.1, p. 2:12 |
| T9 | Clarification | Constraints and patterns hold in every state | §6.1, p. 2:30; §4.2, p. 2:18 |
| T10 | Correction | Default multiplicities: `opt` | §6.1, p. 2:29 |
| T11 | Correction, change | Typos in Definitions 3–5; the effective group | pp. 2:25–2:28 |
| T12 | Clarification | Concrete syntax of the examples | §4, §6.1 |
| T13 | Clarification | Bounded analysis | §6.2, p. 2:32 |
| T14 | Change | The initializer `:=` is the initial value of a reference | §6.1, p. 2:29; §4.1, pp. 2:13–2:14 |

## T1. Instances may reappear (change)

**Paper (Definition 5, item 2, p. 2:28):** "Instances that disappeared cannot reappear."

**Clafer 0.5.6:** an instance may disappear and reappear.

**Why:** Alloy represents an infinite trace as a lasso, a finite prefix whose last state loops back to an earlier state.
Under the rule, a cyclic behaviour such as green, yellow, red, green, … needs a fresh instance of `green` for each cycle, so infinitely many instances, which no lasso over finitely many atoms has.
With the rule, `final xor s` with `initial a -->> b` and `b -->> a` has no trace. Without it, Alloy finds `a, b, a, b, …` at once.

**Consequences:**

- The same instance can have several lifetimes. `initial`, `initially` and `finally` apply to each of them (T7).
- A scope bounds the instance identities across the trace, as in Alloy: an identity may be reused when an instance reappears, and the multiplicities bound the existing instances in each state. So a cyclic behaviour needs no more identities with a longer trace, but an instance that is replaced by another needs one more identity. `item` with `[ initially (all x : item | X no (x ** item)) ]` is mandatory in every state and has one instance in each, yet it has no trace at scope 1 and one at scope 2 (`tmp_scope_identities.cfr`, checked on 2026-11-04 with both scope strategies, 3 to 10 states).
- An instance never changes its parent, also across its lifetimes: for any two states in which an instance exists, its parent is the same. Definition 5, item 3 compares adjacent states only, which allowed no reappearance; without item 2, it must be restated for any two states. In the Alloy output, the parent is a static field (`tmp_parent_across_lifetimes.cfr`).

**Formalized:** a trace has one universe of identities with a fixed type and parent, and a set of live identities in each state; every state of a valid trace is a valid static configuration of its live instances, and a constant trace of a static instance is a trace of the model without temporal constraints ([traces and snapshots](https://github.com/kbak/clafer-semantics/blob/main/docs/behavioral-traces.md)).

## T2. Temporal obligations end with the parent of the context instance (change)

**Paper (§6.1, p. 2:30):** a nested constraint is lifted to the top level as `G (all b : this.B | b => ϕ(b))`, so it applies to every instance of `B` while it exists.
Its temporal operators are not bounded: an `X`, `F` or `U` started while `b` exists must be fulfilled even after `b` has disappeared, and even after `b`'s parent and all its ancestors have disappeared.
For `-->>`, the paper adds that "the context clafer (the source clafer) has to continue to exist until the post-condition is satisfied" (p. 2:31).

**Problem:** unbounded obligations outlive the states that created them.
In a traffic light, `on` contains `normal` and `flashing`, and `normal` has the transition `normal --> flashing`. Switching the light `off` from `normal` leaves a pending obligation `flashing`. That obligation can no longer be met, so the light can never be switched off from `normal`.
A statechart would instead drop the pending transitions of the nested states when their enclosing state is left (preemption).

**Corrected semantics (decided on 2026-11-03):** a constraint holds for every instance of its context clafer in every state in which that instance exists, as in the paper.
Its temporal obligations (`X`, `F`, `G`, `U`) last while the **parent** of the context instance exists, and they lapse when the parent disappears.
This follows the rule that nothing outlives its parent: the constraints of a clafer belong to its parent's lifetime.
Top-level constraints, whose context is the root, keep plain LTL.

In the Alloy output, with `P` = "the parent of the context instance exists":

| Operator | Alloy 6 |
|---|---|
| `X ψ` | `after (not P or ψ)` |
| `F ψ` | `eventually (not P or ψ)` |
| `G ψ` | `(not P) releases (not P or ψ)` |
| `ψ U χ` | `(P and ψ) until (not P or χ)` |

**Consequences:**

- **The paper's examples work as written.** In the power window (Listing 3, p. 2:16, and Listing 4, p. 2:18), `[ req=down --> movingDown ]` under `movingUp` means, as the paper says, that "in the next snapshot the global state will contain movingDown" (p. 2:17): the obligation outlives `movingUp`, because its parent `winStates` still exists.
- **Preemption:** when `on` is left, the pending obligations of the constraints of `normal` and `flashing` lapse, because their parent `on` has disappeared.
- **`-->>`:** `[ a -->> b ]` under `s` keeps `s` and `a` until `b`, as the paper says, unless the parent of `s` disappears first.
- **Constraints about disappearing:** `[ X no this ]` says that the context instance lasts one state, which is meaningful because the obligation outlives the instance.
- **A constraint's timeline:** to make a constraint last longer, the modeller places it higher in the hierarchy, or at the top level.
- **Identities:** a mandatory clafer does not keep its instance. A replacement of the parent ends the obligations of the old one, so a property of a state machine that must hold across replacements quantifies over the instances, e.g. `all m : sm | m.a && go => X (m.b || no (m ** sm))`, or the machine is `final`.

**Negated obligations (decided on 2026-11-04, [gsdlab/clafer#110](https://github.com/gsdlab/clafer/issues/110)):** the table bounds each operator where it is applied, and Alloy negates the result classically.
So `!(F error)` became `always (P and not error)`: the parent could never disappear, whereas `G !error` let it disappear. The two formulas were not equivalent.
The negations are therefore pushed inside the temporal operators first, with the dualities of LTL, and the table applies to the result:

| Formula | Pushed |
|---|---|
| `!X ψ` | `X !ψ` |
| `!F ψ` | `G !ψ` |
| `!G ψ` | `F !ψ` |
| `!(ψ U χ)` | `!χ W (!ψ && !χ)` |
| `!(ψ W χ)` | `!χ U (!ψ && !χ)` |
| `!initially ψ`, `!finally ψ` | `initially !ψ`, `finally !ψ` |

`=>`, `<=>`, `xor`, `if then else` and the quantifiers `all`, `some` and `no` are expanded where a temporal operator is below them; `one` and `lone` keep the classical negation.
So every obligation lapses with the parent, whether it is stated or negated, and the LTL dualities hold.
The price is the law of contradiction: a formula and its negation can both hold, on a lifetime that ends before their obligations are due. `F error && !(F error)` has a trace in which the parent disappears without an error; while the parent exists, it has none.
Making `F` and `U` strong at the end of a lifetime instead would keep the law, but a pending `F` would then keep the parent alive, which contradicts the preemption above.
The negated parts of the patterns follow: in `never p between q and r`, the premise `F r` holds only when `r` occurs while the parent exists.

Checked on 2026-11-04 with Alloy 6.2.0 and claferIG, with both scope strategies, at the scopes 1 to 3 and with 3, 6 and 10 states (`tmp_negated_obligations.cfr` and claferIG's model tests): `(G !error) <=> !(F error)`, `!(X error) <=> X !error` and `!(error U !error) <=> (error W (!error && error))` hold, `[ !(F error) ]` lets the parent disappear, and with a `final` parent `[ F error ]` and `[ !(F error) ]` contradict each other.

**Formalized:** the bound of both tables, pushing the negations first, is the semantics of [attachment and cancellation](https://github.com/kbak/clafer-semantics/blob/main/docs/behavioral-formulas.md#attachment-and-cancellation). It is proved that pushing the negations and then bounding by the parent gives plain LTL formulas with exactly the meaning of the source formula, for every operator, both signs, all bound variables and every state. A cancelled obligation does not resume when the parent reappears. A variable keeps the instance it was bound to across states, while navigation from it reads the current state.

**Clafer 0.5.6 differs (a bug, [gsdlab/clafer#107](https://github.com/gsdlab/clafer/issues/107)):** it bounds the obligations by the context instance itself, not by its parent.
Then `[ req=down --> movingDown ]` under `movingUp` lapses as soon as `movingUp` ends, so it only forces leaving `movingUp`, without fixing the next state.
This was checked with Clafer 0.5.6 and Alloy 6.2.0 on 2026-11-03:

```
go ?
xor sm
  initial a
    [ go --> b ]       // nested in its source state
  b
  c
assert [ sm.a && go => X sm.b ]
```

The assertion has a counterexample, in which `a` is followed by `c`.
Under the corrected semantics it holds at scope 1, and at any scope with `final xor sm` (`tmp_transition_in_source_state.cfr`).
At scope 2, the mandatory machine can be replaced by another instance, which starts again in `a`, and the obligation of the old `a` lapses with its parent: the assertion has a counterexample, while `all m : sm | m.a && go => X (m.b || no (m ** sm))` holds (`tmp_transition_replaced_machine.cfr`). Checked on 2026-11-04 with both scope strategies, at the scopes 1 to 3 and with 3, 6 and 10 states.
Clafer 0.5.6 gets the corrected meaning only for transitions of clafers (T3), which it compiles to constraints of the parent.

## T3. Transitions of clafers (extension)

**Paper:** the grammar scheme of a clafer declaration (§6.1, p. 2:29) has no transition, and the examples write transitions only as constraints.

**Clafer 0.5.6:** a clafer may declare one transition after its multiplicity, e.g. `on --> off`, `initial idle -[ coin ]-> brewing`.
It applies to each instance of the clafer while it exists, and its obligations last while the clafer's parent exists.
So the transition of a nested state disappears when its enclosing state is left.
For `-->>`, the source clafer continues to exist until the target holds, as §6.1 says of the source clafer.
Clafer 0.5.6 compiles it to the constraint `[ on --> off ]` of the parent, which gives this meaning under the 0.5.6 bound. Under the corrected bound of T2, it must be a constraint of the clafer itself: as a constraint of the parent, its obligations would last while the grandparent exists, and the preemption of T2 would be lost.
The transition's constraint spans the clafer and its transition, so an unsat core shows `green --> yellow`.
A clafer has only one transition. More ways out of a state with the same lifetime are constraints in the state, e.g. `[ this -[ g ]-> c ]` in `a`. A constraint `[ a -[ g ]-> c ]` of the parent lasts while the grandparent exists, so it is not preempted when the parent is left (T2). The CheatSheet and ClaferIDE's `CoffeeMachine.cfr` show the form in the state since 0.5.7.

The four arrows desugar as in the paper (§6.1, pp. 2:31–2:32):

| Arrow | Meaning |
|---|---|
| `a --> b` | `a => X b` |
| `a -->> b` | `a => (this && a) U b` |
| `a -[ g ]-> b` | `a && g => X b` |
| `a -[ g ]->> b` | `a && g => (this && a) U b` |

## T4. A chain of transitions is a sequence (change)

**Paper (§6.1, p. 2:31):** `ϕ --> ψ` is `ϕ => X ψ`. Transitions are right-associative, so `a --> b --> c` is `a => X (b => X c)`, a conditional: if `a`, and if then `b`, then `c`.
That contradicts the paper's own scenario `[ sometime closed -->> partlyOpen -->> open ]` (§4.5, p. 2:22), which it reads as closed, then partlyOpen, then open.

**Clafer 0.5.6:** a chain is a sequence. Only its first state is a condition:

```
a --> b --> c        // a => X (b && X c)
a -->> b -->> c      // a => (this && a) U (b && (this && b) U c)
```

A single transition keeps the paper's meaning.
The formalization proves that this expansion of chains keeps the meaning of a chain ([transitions](https://github.com/kbak/clafer-semantics/blob/main/docs/behavioral-surface.md#transitions-and-attachment)).

**Scenarios need an anchor.** A constraint holds in every state (T9), so an unanchored chain says "whenever `green`, this whole sequence follows", which is usually unsatisfiable.
A scenario is anchored with `initially`, e.g. `[ initially (green --> yellow --> red) ]`.
Its first state is a condition, so a scenario states it when the model does not force it, e.g. `[ initially green ]`.

## T5. Assertions hold for all traces; possible scenarios are constraints (correction)

**Paper:** it describes assertions in two incompatible ways.

- §4.5 (p. 2:21): scenarios are assertions "checked for consistency with the rest of the model, as opposed to being enforced on all executions". `assert [ sometime closed -->> partlyOpen -->> open ]` "holds … if there exists an execution" through those states.
- §4.5 (p. 2:22): the negative scenarios with `never` are safety properties, which must hold on all executions.
- §6.1 (p. 2:30): an assertion "is checked by the compiler, and an error is reported if it is inconsistent with the model."

**Clafer 0.5.6:** an assertion must hold for all traces. The Alloy output has a `check` for each assertion, including nested ones, which hold for each instance of their clafer (T2).
claferIG's `check` runs them within the scopes and the maximum trace length, and a failed assertion gives a counterexample trace.

A scenario that should be possible is a constraint in a separate model, which imports the model. It is possible if that model has a trace:

```
//# OPTIONS --import=window.cfr
[ initially (sometime (w.closed && F (w.partlyOpen && F w.open))) ]
```

This was checked on 2026-11-03 on a three-state window, and once on a variant that cannot reach `open`:

| Form | Window | Window that cannot open |
|---|---|---|
| The paper's `assert [ sometime closed -->> partlyOpen -->> open ]` | counterexample | counterexample |
| The scenario model above | trace | no trace |

The paper's assertion fails in both models, because not every trace reaches `open`, e.g. a window that stays closed. The scenario model tells the two models apart.

**Formalized:** an assertion fails exactly when some trace of the model is a counterexample, and a scenario is possible exactly when the model with the scenario's constraints has a trace ([models, assertions and scenarios](https://github.com/kbak/clafer-semantics/blob/main/docs/behavioral-surface.md#models-assertions-and-scenarios)). A counterexample is a trace on which the assertion does not hold, i.e. the classical negation of the whole assertion, not the assertion with a source `!` pushed inside as in T2.

## T6. The negative scenarios and the model-checking recipe (correction)

**Paper (§4.5, p. 2:22):** "it is impossible that the user requests to open the window, and the window remains closed in the next step" is written `assert [ never req = down --> closed ]`.

Transitions bind more loosely than everything else, so this parses as `(never req = down) --> closed`.
Even as `never (req = down --> closed)`, it fails in every state where `req` is not `down`, because the transition holds there trivially.
The same mistake was in the wiki's power window page (`wc3`, `wc5`).
Correct forms:

```
assert [ req = down --> no closed ]
assert [ never (req = down && X closed) ]
```

On the window model (2026-11-03), the paper's form gives a counterexample, both correct forms hold, and the false `assert [ never (closed && X closed) ]` gives a counterexample.

The paper's other example, `assert [ never closed && cmd=motorUp ]`, parses as intended: `never` takes the whole conjunction.

**Model checking (p. 2:22):** "To model check property ϕ, add … assert [ never ¬ϕ ]".
`never ¬ϕ` is `G ϕ`, which requires `ϕ` in every state, not only from the start of the trace.
For a temporal property of the trace, write `assert [ initially ϕ ]`.
On the window model, whose `closed` is `initial`, `assert [ initially w.closed ]` holds, while the recipe's `assert [ never !w.closed ]` gives a counterexample, since the window opens later.

## T7. `initially` holds in the first state of each lifetime (correction)

**Paper (§6.1, p. 2:31):** `[ initially ϕ ]` desugars to `[ (no this && X this) => X ϕ ]`.
An instance that exists in the first state of the trace was never absent before, so the premise never holds and `ϕ` is never required.
That contradicts §4.1 (p. 2:13): `initial stopped` means that "the first snapshot of every trace will contain an instance of stopped".
For the top level, the paper says that `initially` "simply prevents adding the default G".

**Clafer 0.5.6:** `initially ϕ` requires `ϕ` in the first state of each lifetime of the context instance: at the start of the trace, or when the instance appears or reappears (T1).
At the top level, it is the start of the trace.
`initial c` requires an instance of `c` whenever its parent's lifetime begins.
`finally ϕ` follows the paper: `ϕ` holds in the last state before the context instance disappears, and it is vacuous for an instance that never disappears.
The formalization has the same anchors: they concern the context instance's own lifetimes, while the cancellation of T2 concerns its parent's ([anchors](https://github.com/kbak/clafer-semantics/blob/main/docs/behavioral-surface.md#transitions-and-attachment)).

## T8. `final` (clarification)

**Paper (§6.1, p. 2:32):** `final D` under `C` adds `[ let di = this.d | X (di = this.d) ]` to `C`: the instances of `D` do not change.
The examples use it for static structure: "the architecture is static" (p. 2:12), and `final` is inherited from the super clafer (p. 2:12).

**Clafer 0.5.6:**

- **Shallow:** `final` fixes the instances of the clafer and its reference, not its children. To fix a feature model, mark each feature `final`, e.g. `final EU ?`. A feature then has one value per trace and may have another value in another trace.
- **Lifetime:** with T1 and T2, the instances of a `final` clafer do not change while its parent instance exists. A parent that reappears may come back with other instances. A `final` clafer whose ancestors are all `final` exists unchanged in the whole trace, and the Alloy output makes its relation static.
- **Inheritance:** `final` and `initial` are inherited from the super clafer, as in the paper. A refinement can add `final`, `finalref` or `finaltarget` to the reference that it inherits, e.g., `final motor : engine` under `abstract engine -> Engine`. Clafer 0.5.6 fixed only a reference that the clafer declares, so such a `final` fixed the instances of `motor` but not their reference, and `finalref` and `finaltarget` were ignored ([gsdlab/clafer#109](https://github.com/gsdlab/clafer/issues/109), fixed in 0.5.7).
- **Extensions:** `finalref` fixes only the reference of each instance, while that instance exists. `finaltarget` fixes only the set of targets of the instances in their parent, while the parent instance exists: the instances may change and swap their targets, but a new instance points to one of the targets. `final` implies both. The paper does not define these modifiers. Up to 0.5.6, `finaltarget` fixed the reference of each instance, as `finalref` does; the distinction follows [kbak/clafer-semantics#127](https://github.com/kbak/clafer-semantics/issues/127) (0.5.7).
- **Enumerations:** in dynamic models, the literals of an `enum` are final ([gsdlab/clafer#92](https://github.com/gsdlab/clafer/issues/92)). In static models, they are not, so that they do not make a static model dynamic.

The paper's rewrite has a typo: `this.d` should name `D`.

**Formalized:** `final`, `finalref` and `finaltarget` as above, including the inherited ones; their expansions into constraints are proved to keep their meaning ([modifiers](https://github.com/kbak/clafer-semantics/blob/main/docs/behavioral-surface.md#modifiers-and-anchors)).

## T9. Constraints and patterns hold in every state (clarification)

**Paper (§6.1, p. 2:30):** a nested constraint is lifted with `G`, and "top-level constraints that have not been lifted are preceded by the LTL quantifier G".
Dwyer's patterns are "just a syntactic sugar exercise" (§4.2, p. 2:18).

**Clafer 0.5.6:** as in the paper, but the paper does not spell out what this means for patterns.
A pattern without a scope holds on the whole trace from each state in which its constraint applies.
So at the top level, `[ sometime d ]` is `G F d`: `d` again and again.
For "once", write `[ initially (sometime d) ]`.
The scope `after q` starts at the first `q`, so at the top level each `q` starts a scope of its own, and `[ initially (s must precede p after q) ]` starts at the first `q` of the trace.
Two expansions of Dwyer's patterns did not follow the scopes up to 0.5.6; 0.5.7 corrects them ([kbak/clafer-semantics#127](https://github.com/kbak/clafer-semantics/issues/127)):

- `s must follow p between q and r` checked only a `p` in the state of `q`: the brackets of Dwyer's `[]((Q & !R & <>R) -> ((P -> (!R U (S & !R))) U R))` were misplaced. Each `p` up to the next `r` needs an `s` before that `r`.
- `s must precede p after q` was Dwyer's `[]!Q | <>(Q & (!P W S))`, which may start the scope at a later `q`, so q, p, q, s held. It starts at the first `q`: `<>Q -> (!Q U (Q & (!P W S)))`, as `lonce p after q` does. For the other patterns, a later `q` gives the same result.

The formalization defines all six patterns in all five scopes over intervals of states, independently of their expansions into LTL, and proves that the expansions agree with these definitions for both signs ([patterns and scopes](https://github.com/kbak/clafer-semantics/blob/main/docs/behavioral-surface.md#patterns-and-scopes)).

The test `tmp_betweenand01.cfr` had `[ sometime d ]` next to `always c between d and e` under an `xor`, which made it unsatisfiable. It now uses `initially`.

## T10. Default multiplicities: `opt` (correction)

**Paper (§6.1, p. 2:29):** "The default multiplicity is 1..1 for clafers whose parent have group cardinality 0..∗, and 0..1 otherwise". The group keywords listed are `xor`, `or` and `mux`.

**Clafer 0.5.4 and later:** `opt` is a group keyword too, meaning `0..*`, and its children are optional by default.
This agrees with the static paper (Bąk et al. 2016, Appendix 3).
The paper's interval rule ignores `opt`. It was the compiler's rule from 0.3.3 to 0.5.3, and with it `opt` had no effect.
For numeric groups, the paper's rule is the tools' rule (S1 and S2 in the [static errata](static-semantics-errata.md)).

## T11. Typos in Definitions 3–5 (correction)

- **Definition 3, item 4 (p. 2:25):** local injectivity needs `i2 ≠ i3`. Without it, `i2 = i3` requires `L(i2) ≠ L(i2)`. It also applies only to set references (`->`), since a bag reference (`->>`) may point to the same target more than once.
- **Definition 3, item 6 (a change, not a typo):** it applies the group of every clafer that types an instance over that clafer's own children. The tools count the own and the inherited children against the effective group (S3 in the [static errata](static-semantics-errata.md)), which changes the meaning of the definition.
- **Definition 4 (p. 2:28):** in the case `e1 in e2`, `{i | ∃. (i, π) ∈ …}` lacks the bound variable: `∃π`.
- **Definition 5, item 2 (p. 2:28):** `∀l > j. i ∉ I_j` should be `i ∉ I_l` (the item is dropped anyway, T1).

## T12. Concrete syntax of the examples (clarification)

- **Precedence:** transitions bind more loosely than every other operator. `initially green --> yellow` is `(initially green) --> yellow`, so a scenario is written `initially (green --> yellow)`. `X a || b` is `(X a) || b`.
- **`xor` after a transition:** a clafer declaration that starts with `xor` cannot follow a clafer with a transition, because `xor` continues the transition's expression. Declare it first, or write the transition as a constraint.
- **Negation:** `not audible` (p. 2:20) is the quantifier `not`, the same as `no audible`.

## T13. Bounded analysis (clarification)

**Paper (§6.2, p. 2:32):** the semantics is over infinite traces, while the implementation uses a bounded state space.

**Clafer 0.5.6:** the Alloy output looks for lasso traces of up to `--tl` states (10 by default) within the scopes, which bound the instance identities across the trace (T1). The simple scope analysis computes the scopes from the multiplicities, which bound the instances in a state, so a model that replaces instances may need larger scopes than it infers.
"No counterexample" from claferIG's `check` holds only within the scopes and the maximum trace length.
The Choco backend does not support temporal models.

**Formalized:** evaluating a formula on a lasso gives exactly its truth on the infinite trace that the lasso represents, including the births, deaths and cancelled obligations at the loop ([finite verification](https://github.com/kbak/clafer-semantics/blob/main/docs/behavioral-verification.md)). This is about one given lasso: not every infinite trace is a lasso, and finding no lasso within a bound does not show that there is no trace.

## T14. The initializer `:=` is the initial value of a reference (change)

**Paper (§6.1, p. 2:29):** the initializer sets the value of a reference: "constant `= exp` and default `:= exp`". The paper gives `:=` no semantics. §4.1 (pp. 2:13–2:14) explains why Clafer has initial clafers instead of default values: a default would need soft constraints, in a language of hard constraints.

**Clafer 0.5.8:** `x -> T := e` gives `x` the value `e` in the first state of each of its lifetimes, as `initially` does for the context instance (T7), and leaves the later values free ([kbak/clafer-semantics#164](https://github.com/kbak/clafer-semantics/issues/164), [initial-value.md](initial-value.md)):

- It is `[ initially this.dref = e ]` in the context of `x`, with `e` resolved in the context of the parent, where it is written: `this` is the parent instance, and a name `y` is the sibling of `x` even if `x` has a child `y`. In the parent's context, `initially` would apply to the first state of the parent's lifetime, so an `x` created later would get no value.
- A set initializer, `xs -> T * := e`, constrains the set of the instances under the parent: `[ initially (some xs => xs.dref = e) ]` in the parent's context. The instances created later are not initialized.
- The reference of a `final` or `finalref` clafer does not change (T8), so it keeps the value that `e` has when its lifetime starts, also when `e` changes later; `= e` would contradict the modifier then. With a constant `e`, `:=` and `=` are the same there.
- A static model has a single state, so `:=` is `=`. An initializer does not make a model temporal.

Up to 0.5.7, `:=` compiled to an assertion `[ some x => x.dref = e ]` in every output ([gsdlab/clafer#116](https://github.com/gsdlab/clafer/issues/116)), so a model with another value had instances and a counterexample. A subclafer cannot replace an inherited `:=` (pure strengthening, reading A in kbak/clafer-semantics#164): its own `:=` or `=` is added to the inherited one, so `= 2` under `:= 2` fixes the value in every state, and `:= 3` has no instance.

## Differences of Clafer 0.5.6 from these errata

- **The bound of the obligations (T2, T3):** Clafer 0.5.6 bounds the obligations of a constraint by its context instance instead of the parent of that instance, and compiles the transitions of clafers to constraints of the parent. Its CHANGES and CheatSheet describe that behaviour. Fixed in 0.5.7: [gsdlab/clafer#107](https://github.com/gsdlab/clafer/issues/107) (2026-11-03).
- **Negated obligations (T2):** Clafer 0.5.6 and the first fix of #107 negate the bounded operators classically, so `!(F error)` keeps the parent alive. Fixed for 0.5.7: [gsdlab/clafer#110](https://github.com/gsdlab/clafer/issues/110) (2026-11-04).

## Formalization

[clafer-semantics](https://github.com/kbak/clafer-semantics) formalizes these errata as its behavioral profile `behavioral-0.5.7-candidate/v1`, compared with clafer at commit `af858ec` (2026-11-05). [From structure to behavior](https://github.com/kbak/clafer-semantics/blob/main/docs/structure-and-behavior.md) explains how the temporal semantics extends the static one, and [key proved properties](https://github.com/kbak/clafer-semantics/blob/main/docs/proved-properties.md) lists the main theorems.
At that commit, two expansions of patterns and `finaltarget` still differed from the profile; clafer `b2875f3` and `8a12ae7` correct them (T8, T9), which the formalization confirms from the source.
The later 0.5.7 commits that change the Alloy output of temporal models, top-level constraints as `always (...)` (`c7a2fb7`) and references to a union of targets with a nested clafer (`2c80226`), were qualified against the profile in [kbak/clafer-compiler-lean#95](https://github.com/kbak/clafer-compiler-lean/issues/95). The pin moves to the 0.5.7 release in [kbak/clafer-semantics#148](https://github.com/kbak/clafer-semantics/issues/148).

[clafer-compiler-lean](https://github.com/kbak/clafer-compiler-lean) is a second compiler of temporal models to Alloy 6, proved against the formalization: a lasso found by Alloy decodes to a valid trace that keeps the same identities in all states, and every model, scenario or assertion counterexample within the scopes and the trace length has a lasso. See its [lessons](https://github.com/kbak/clafer-compiler-lean/blob/main/docs/lessons.md) for the exact conditions.
Neither proof covers the Haskell compiler or claferIG; they agree with the formalization on the compared cases and on the checks in these errata.

## Open

- **Scenarios in claferIG (T5):** a possible scenario is checked by solving a separate model that imports the model. claferIG's `check` covers only assertions, which hold for all traces.
- **Undefined values:** the formalization keeps definedness apart from truth: a division by zero, or an integer taken from an empty or multiple reference, is undefined, not false, also inside a temporal formula. The Alloy output of clafer has no undefined values, and it was not compared with the formalization on such models.

## Sources

- clafer's [CHANGES.md](../CHANGES.md), version 0.5.6, which lists T1–T4 (T2 with the 0.5.6 bound).
- clafer's [CheatSheet](CheatSheet.md), section "Temporal models".
- The temporal generator [AlloyLtl.hs](../src/Language/Clafer/Generator/AlloyLtl.hs) (its header comment lists T1 and T2), and the transitions in [Desugarer.hs](../src/Language/Clafer/Intermediate/Desugarer.hs) (`desugarTrans'`, T4).
- The temporal test models `test/positive/tmp_*.cfr`, fixed against the paper in 0.5.6. The traffic lights are split into one file per model, with their scenarios in files that import them.
- The checks of T2, T5 and T6 were run with Clafer 0.5.6 and Alloy 6.2.0 on 2026-11-03; those of T1, T2 (negations, replaced machines) and T3 with Clafer 0.5.7 on 2026-11-04.
- clafer-semantics: [behavioral-profile.md](https://github.com/kbak/clafer-semantics/blob/main/docs/behavioral-profile.md), [structure-and-behavior.md](https://github.com/kbak/clafer-semantics/blob/main/docs/structure-and-behavior.md), [proved-properties.md](https://github.com/kbak/clafer-semantics/blob/main/docs/proved-properties.md), and the review of the pattern and modifier choices in [kbak/clafer-semantics#127](https://github.com/kbak/clafer-semantics/issues/127); clafer-compiler-lean: [lessons.md](https://github.com/kbak/clafer-compiler-lean/blob/main/docs/lessons.md).
- The review of these errata against the implementation, [gsdlab/clafer#111](https://github.com/gsdlab/clafer/issues/111), and the regression qualification on [gsdlab/clafer#107](https://github.com/gsdlab/clafer/issues/107).
