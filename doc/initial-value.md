# The initializer `:=` as an initial value

Status: implemented in 0.5.8, as agreed in
[kbak/clafer-semantics#164](https://github.com/kbak/clafer-semantics/issues/164). For
redefinition, the decision is reading A, pure strengthening (see
[Inheritance and redefinition](#inheritance-and-redefinition)).
It changes the meaning of `:=` from a default, which no backend supports, to the initial value of
a reference: the same as `=` in static models, and the value in the first state of each lifetime
of the clafer in temporal models. True defaults, preferred unless something else is required,
need soft constraints, a separate language extension left as future work. The sections up to
[Implementation](#implementation) are the proposal; [What 0.5.8 does](#what-058-does) records the
choices of the implementation.

## Before 0.5.8

The grammar ([src/clafer.cf](../src/clafer.cf)) has two initializers of a reference clafer:

```
Init ::= InitHow Exp ;
InitConstant. InitHow ::= "=" ;
InitDefault.  InitHow ::= ":=" ;
```

`=` is a constant. The desugarer (`desugarInit` in `Intermediate/Desugarer.hs`) turns
`x -> integer ? = 10` into a constraint in the context of the parent:

```
[ some x => x.dref = 10 ]
```

The constraint does not require `x`: an optional clafer stays optional, and the value applies
when the clafer exists (`test/positive/optionalClaferInitializer.cfr`). In a temporal model, it
holds in every state (errata T9), e.g., the Alloy output of `level -> integer = 3` nested in
`Light` is `always (self_ in alive_Light implies ((some self_.r_level) => … = 3))`.

`:=` is meant as a default: the value of the reference unless something else is required. The
paper's logic has no defaults, the cheat sheet says that no backend supports them, and the
desugarer does not reject `:=` either. It builds the same constraint as for `=`, but with
`_isHard = False`, the flag of assertions. So `:=` is silently an assertion in every output:

| Output | `x -> integer := 10` |
|---|---|
| `-m clafer` | `assert [((#x) >= 1) => (x.dref = 10)]` |
| `-m alloy` | `assert assertAt_1_14 { (some x) => ((x.@x_ref) = 10) }` and `check assertAt_1_14 for 1` |
| `-m choco` | `assert(implies(some(global($x)), equal(joinRef(global($x)), constant(10))))` |

With `[ x = 5 ]`, the model has instances, and the assertion gives a counterexample. Neither
reads as a default. No model in the tests or on the wiki uses `:=`; only the cheat sheet
mentions it.

## Proposal

`x -> T := e` gives `x` the value `e` when `x` comes into existence, and leaves the value free
afterwards.

- **Static models:** a static model has a single state, in which the value of `x` is its initial
  value. So `:=` is the same as `=`: `[ some x => x.dref = e ]`, a hard constraint. The model
  stays static, and Choco can solve it.
- **Temporal models:** `x` has the value `e` in the first state of each of its lifetimes, and may
  change in the next state. A transition, a constraint or nothing at all decides the later
  values.

A model is temporal when it has a temporal operator or modifier, as decided by
`staticClaferSubset` in `Language/Clafer.hs`. The initializer must not count: `:=` alone does not
make a model temporal.

### Where the constraint goes

Your first reading puts the constraint in the context of the parent:

```
x -> integer ?
[ initially (some x => x.dref = 10) ]
```

`initially` holds in the first state of each lifetime of the *context* instance (errata T7),
here the parent. An `x` that appears later in the parent's lifetime would get no initial value,
and a top-level `x` that appears after the first state neither. (The form
`initially x.dref = 10`, without `some x =>`, would in addition require `x` in the first state,
which goes against its `?`.)

The constraint belongs in the context of `x` itself, so that each lifetime of `x` begins with
the value:

```
x -> integer ?
    [ initially this.dref = 10 ]
```

For a `level` nested in `Light` with `[ initially this.dref = 3 ]`, the Alloy output is
`all self_ : level | always (self_ in alive_level implies ((not before self_ in alive_level) implies ((self_.@level_ref) = 3)))`.
Checked with claferIG on

```
level -> integer ?
    [ initially this.dref = 3 ]
[ initially no level ]
[ F some level ]
```

all 428 traces at scope 1 (10 states) create `level` with the value 3, and its value changes
736 times in them while `level` exists.

`some x =>` is not needed: the constraint is evaluated for each instance of `x`.

### Name resolution of the expression

With `=`, the expression `e` is resolved in the context of the parent, where `this` is the
parent instance. In the context of `x`, `this` is the instance of `x`. The desugarer must keep
the meaning of `e`:

- `this` in `e` becomes `this.parent`, and `parent` becomes `this.parent.parent`.
- A bare name that the parent's context resolves to one of its children, e.g. a sibling `y` of
  `x`, resolves from `x` by the ancestor strategy to the same clafer (`this.parent.y`), unless
  `x` has a descendant of the same name, which the descendant strategy finds first. The
  desugarer can prefix such names with `parent`, or the resolver can resolve `e` in the
  parent's context before the constraint is moved; the second keeps the rules of the name
  resolver specification unchanged.

Constants, enumeration literals and top-level clafers resolve the same in both contexts.

### Cases

| Declaration | Static model | Temporal model |
|---|---|---|
| `x -> integer := 10` | `[ some x => x.dref = 10 ]` (= `x -> integer = 10`) | `x` nested `[ initially this.dref = 10 ]` |
| `x -> integer ? := 10` | as above | as above; `x` may be absent |
| `xs -> integer * := 1, 2` | `[ some xs => xs.dref = 1, 2 ]` | `[ initially (some xs => xs.dref = 1, 2) ]` in the parent's context |
| `finalref x -> integer := 10`, `final x …` | as `=` | as above (initially); the value then stays (see What 0.5.8 does) |
| `x -> integer = 10` | unchanged | unchanged: every state |

A set initializer constrains the set of all the instances of `xs` under the parent, so it stays
in the parent's context: `initially` then applies to the first state of the parent's lifetime.
Instances of `xs` created later are not initialized; each of them would need its own value,
which `1, 2` does not give. The documentation should say so.

### Inheritance and redefinition

An initializer in an abstract clafer applies to the instances of all its subclafers, as `=`
does. A subclafer cannot replace it: its own initializer or constraint on the same reference is
added to the inherited one, and two different initial values have no instance.

**Decision: reading A, pure strengthening** (#164). As for the other redefinitions, a subclafer
must satisfy the inherited initializer, and every instance of it is a valid instance of the
abstract clafer. A subclafer's own `:=` or `=` on the reference is added to the inherited
initializer, never replaces it: under `abstract val -> integer := 2`, `fixed : val = 2`
strengthens the initial value to the value in every state, while `= 3` or `:= 3` has no instance.
A different value needs a different structure, e.g. an intermediate abstract clafer that holds the
initializer, which the overriding clafer does not inherit. Reading B, a default guarded by the
subclafers that redefine it (`initially (this not in override => this.dref = 2)`), is rejected:
it is not monotone. 0.5.8 already behaves as reading A, since it keeps both the inherited and the
own constraints; it reports a conflicting value as a model with no instance, not as an error.

### The explicit form

`-m clafer` prints the desugared constraint, so the explicit model has no `:=` and compiles to
itself, as now. For a temporal model, it shows `[ initially this.dref = 10 ]` nested in `x`.

## Compatibility

- A model that uses `:=` changes from an assertion to a constraint: what was checked becomes
  required. No model in the tests or on the wiki uses `:=`.
- A static model with `:=` now behaves as with `=`.
- The cheat sheet says that `:=` is a default that no backend supports, in the section on
  initializers and in the table of supported features. Both change.

## Implementation

1. `desugarInit`: for `:=`, build a hard constraint. Whether the model is temporal is known only
   after desugaring, so either
   - mark the constraint as an initializer in the IR, let `iExpBasedChecks` ignore its
     `initially`, and drop the `initially` in static models before the generators run, or
   - decide temporality on the AST before desugaring, without the initializers, and pass it to
     the desugarer.
   The second is simpler. The first keeps the desugarer independent of the rest of the model.
2. Place the single-reference initializer in the clafer's own elements, and keep the
   expression's meaning as described above.
3. Warn for `:=` on a `final` or `finalref` clafer. (Not done: `:=` is not redundant there, see
   What 0.5.8 does.)
4. Documentation: the cheat sheet, and a short section in the temporal semantics errata, next to
   T7.

## Tests

- Static: `x -> integer := 10` gives the same explicit model and the same instances as `= 10`;
  with `[ x = 5 ]`, no instance. The model has Choco output.
- Temporal: the `level` model above, a mandatory `x` (value in the first state, changed later),
  an `x` under a parent that is replaced (each lifetime starts with the value), and a
  `finalref` reference (constant).
- Name resolution: an initializer `:= y` with a sibling `y` of `x`, and with a child `y` of `x`.
- A set initializer.
- Negative: `:=` on a clafer that is not a reference, which `=` rejects with a type error
  (`x = 10`: "Function '=' cannot be performed on TClafer … = TInteger").

## What 0.5.8 does

- **Temporality:** the desugarer already desugars a model twice when it is dynamic (for the final
  enumerations): first as a static model, in which `:=` is `=`, and again as a dynamic one if the
  first result has a temporal operator or modifier. So an initializer does not make a model
  temporal, and the IR needs no mark for initializers.
- **Name resolution:** the desugarer puts `[ initially this.dref = initvalue(e) ]` in the elements
  of `x`. `initvalue` is a mark that only the name resolver sees: it resolves `e` in the
  environment of the parent, as for `=`, and then replaces `this` with `this.parent` (the root
  for a top-level clafer). After name resolution, every relative name is a path from `this`, so
  the rewritten `e` means the same in the context of `x`. The rules of the name resolver are
  unchanged. E.g., in `A` with `y -> integer` and `x -> integer ? := y + 1` with a child
  `y -> integer`, the explicit model has
  `[initially (this.dref = (this.parent.A__y.dref + 1))]` in `x`.
- **Sets:** an initializer is a set initializer when the multiplicity of `x` allows more than one
  instance (an upper bound above 1, or `*`). An abstract clafer has no multiplicity of its own, so
  the initializer of `abstract Val -> integer := 2` gives each instance of a subclafer its initial
  value.
- **`final`, `finalref`:** `:=` is an initial value as for any reference, and the modifier keeps
  it: the reference has the value that `e` has when its lifetime starts, for the whole lifetime.
  The proposal made `:=` the same as `=` here, which holds only for an `e` that does not change:
  with `finalref x -> integer := y`, a `y` that is 2 when `x` appears and 3 later leaves `x` at 2,
  whereas `= y` would contradict `finalref` (the review in
  kbak/clafer-semantics#164). So there is no warning
  either (`tmp_initialValue04.cfr`).
- **Outputs:** `:=` is a hard constraint in every output; no initializer becomes an assertion.
  Choco supports the static models, as for `=`.
- **Tests:** `initialValueStatic.cfr` (the same outputs and instances as with `=`), and
  `tmp_initialValue01.cfr` to `tmp_initialValue06.cfr`: an optional `level` created later, a
  mandatory `x` whose value changes, a `level` whose parent is replaced, `finalref` and `final`
  references, set initializers, and the name resolution (`this`, a sibling and a child with the
  same name, an abstract clafer). `case_InitialValue` in the test suite compares the outputs.
