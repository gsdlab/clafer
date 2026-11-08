# Decimal numbers in the Choco backend: a fixed-point `decimal` type

Status: implemented in 0.5.5 (Oct 26, 2026): clafer gsdlab/clafer#102, chocosolver gsdlab/chocosolver#39,
claferIG gsdlab/claferIG#39, the editors and the web tools. This document describes the implementation;
[Changes from the draft](#changes-from-the-draft) lists where it differs from the plan.

## Goal

A new primitive type, `decimal`: numbers with a fixed number of decimal digits. Models with
`decimal` clafers and decimal literals compile with `clafer -m choco` and solve in chocosolver,
with the same features as integers: enumeration, `sum`/`min`/`max`, sets and joins, quantifiers,
single- and multi-objective optimization, unsat cores.

`real` and `double` keep their meanings and stay unsupported in both backends:

* `real` is the mathematical reals, reserved for native real variables (choco's `RealVar`, Ibex).
* `double` is IEEE 754 binary floating point, for which neither backend has a solver.

The name says what is supported: `decimal`, like SQL's `DECIMAL`, is exact base-10 arithmetic, so
`0.1 + 0.2 = 0.3` holds, which it does not for IEEE doubles. Calling the fixed-point type `double`
would mislead (decided Oct 26, 2026).

## Types

* **Order:** `integer ⊂ decimal ⊂ real` and `double ⊂ real`; `integer` also converts to `double`,
  as today. Every integer is a decimal and every decimal is a real.
* **`decimal` and `double` are incomparable:** most decimals are not doubles (0.1 is 1/10, and a
  double's denominator is a power of 2), and doubles need more digits and a larger range than a
  model's decimals. They have no common type (the type checker gives their union), so
  `decimal + double` is refused by both backends, which refuse doubles, as C# refuses mixing
  `decimal` and `double` without a conversion.
* **Literals:** a plain decimal literal (`19.99`, the `PosReal` token) is a `decimal`; it is exact,
  and it widens to `real` where a real is expected, so `R -> real = 3.1415` still type-checks. An
  exponent literal (`1.5e-3`, `PosDouble`) stays a `double`. There are no `real` literals any
  more: real values come only from references to `real`. `IReal` stays in the IR, next to
  `IDecimal` and `IDouble`, for a future backend with native real variables.
* **Reserved name:** `decimal` joins the primitive names, so a model with a clafer named `decimal`
  stops compiling.

## Semantics

A decimal has **`k` fractional digits**, the same `k` for the whole model (the *scale*).
Internally it is the integer `v · 10^k`: with `k = 2`, `1.99` is `199`.

* `+`, `-`, unary `-`, comparisons, `sum`, `min`, `max`, `%` and multiplication by an integer are
  exact.
* `decimal * decimal`, and division with a decimal or variable divisor, **round** the result to
  `k` digits, half away from zero (`1.99 * 1.99 = 3.9601 → 3.96`, `0.50 * 0.25 = 0.125 → 0.13`,
  `-19.99 * 0.13 = -2.5987 → -2.60`), like SQL `DECIMAL` arithmetic.
* Rounding half away from zero was chosen over truncation (Oct 26, 2026): decimals will mostly be
  attributes that are summed and optimized, and truncation pulls every product toward zero by up
  to a whole step, so its errors add up in one direction (ten items of `19.99 * 0.13` sum to 25.90
  instead of 25.987; rounding gives 26.00) and bounds like `price * rate <= 2.59` are consistently
  too lenient. Rounding errs by at most half a step, either way.
* A constraint holds only on the grid: `x * x = 2` has no instance, and `x = 1.0 / 3` has
  `x = 0.33`. An operation on two integers stays an integer operation: `x = 1 / 3` is `x = 0`, as
  today.
* Equality stays exact, after rounding (decided Oct 26, 2026). A model that needs an approximate
  equality uses more digits (`--decimal-digits=4` gives `x = ±1.4142` for `x * x = 2`) or a
  tolerance with two inequalities (`[ x * x >= 1.98 && x * x <= 2.02 ]`); chocosolver's README and
  clafer's CheatSheet document both.

## Scale rules

### The model scale `k`

* Inferred by clafer: the largest number of fractional digits among the model's decimal literals,
  as written (decided Oct 26, 2026). `rate = 1.995` gives `k = 3`, `price = 2.50` gives `k = 2`,
  and a model with only `12.5` gives `k = 1`, so `12.5 * 0.5` is `6.3`.
* A model with decimals but no fractional literals (`x -> decimal` with `[ x = 3 ]`, or no
  literals) has `k = 0`: its decimals are integers and `decimal * decimal` rounds to integers.
* Overridden with a new clafer option `--decimal-digits=k` (passed to the JS as
  `decimalScale(k)`); chocosolver's command line gets `--decimal-digits` too, like `--maxint`.
* A literal with more digits than an explicit `k` is an error, not silently rounded.
* The digits are counted as written, so trailing zeros count (`2.50` is 2 digits). `IReal` holds a
  `Double`, which has lost them (`2.50` and `2.5` are the same value), so a decimal literal
  becomes a new `IDecimal` that keeps the literal exactly (e.g., the digits as an `Integer` and the
  number of fractional digits).

### Types of expressions

Every numeric expression is either an **integer** (scale 0) or a **decimal** (scale `k`); rounding
after each `*` and `/` keeps every decimal at scale `k`, so there is no per-expression scale to
track. `s = 10^k`; `rdiv(n, d)` is division rounded half away from zero.

| expression | result | compiled as |
|---|---|---|
| integer in a decimal context | decimal | `x · s` (exact) |
| `a ± b`, `-a`, `a < b`, `a = b`, ... | decimal | `a ± b`, ... |
| `decimal * int`, `int * decimal` | decimal | `a · b` (exact) |
| `decimal * decimal` | decimal | `rdiv(a · b, s)` |
| `decimal / int` | decimal | `rdiv(a, b)` |
| `int / decimal` | decimal | `rdiv(a · s², b)` |
| `decimal / decimal` | decimal | `rdiv(a · s, b)` |
| `decimal % decimal` | decimal | `a % b` |
| `decimal % int`, `int % decimal` | decimal | `a % (b · s)`, `(a · s) % b` |
| `sum`, `min`, `max` of refs to decimals | decimal | unchanged |
| `product` of refs to decimals | — | type error in the first version (rounding after each factor does not fit the `Product` monoid) |
| `if c then a else b` | the common type | branches converted |
| `in`, `not in`, set `=`, `++`, `--`, `**` over decimals | decimal | unchanged, when both sides are decimals, or the integer side is a constant or a single value; a set of integers against a set of decimals is a type error |
| `#` | int | unchanged |
| anything with a `double` or a `real` | — | unsupported (no Choco output) |

`a · b` and `a · s` must not overflow: type analysis lowers `decimal * decimal` and divisions with a
decimal to the AST operators `DecimalMul` and `DecimalDiv`, and an integer in a decimal context to
`x * 1.0`, so the lowering is the same when the types are analyzed again. Their IR node
`IrDecimalArithm` compiles to the propagators `PropDecimalMul` (`z = rdiv(x · y, s)`) and
`PropDecimalDiv` (`z = rdiv(x · s, y)`), which reason on the bounds with `long` arithmetic, so the
intermediate product never becomes a variable. Division by zero keeps the current guard (the
divisor is 1, or 1.0, outside the clafer's instances).

## Range

* **Choco's limit:** an `IntVar` is bounded by `IntVar.MAX_INT_BOUND = Integer.MAX_VALUE / 100 =
  21,474,836`. Every scaled value must fit: with `k = 2`, decimals are within about ±214,748.36;
  with `k = 4`, about ±2,147.48.
* **Decimal range:** the values of decimal refs lie in `[decimalLow, decimalHigh]`. By default
  (decided Oct 26, 2026) it is the largest range whose scaled values fit choco's bound, leaving one
  value for the uninitialized ref: `B = MAX_INT_BOUND - 1 = 21,474,835`, scaled domain `[-B, B]`,
  so ±214,748.35 with `k = 2`, ±2,147,483.5 with `k = 1` and ±21,474,835 with `k = 0`. It does not
  depend on the int range. The JS `decimalRange("low", "high")` narrows it; there are no clafer or
  chocosolver options for the range yet. chocosolver rejects a scale whose range does not fit.
* **Bounded domains:** `IrCompiler.intVar` created enumerated choco domains for bounded IR
  domains, but the default range has about 43 million values, a 5 MB bitset per variable. Every
  interval domain with more than 2^16 values, decimal or not, now gets a choco *bounded* domain
  (`intVar(name, lb, ub, true)`), which propagates bounds only, and multiplication no longer
  enumerates more than 2^16 products. This suits arithmetic and comparisons; holes (`x != 1.5`,
  membership in a few constants) are only enforced on instantiation.
* **Results beyond the bound:** a decimal ref cannot be beyond the range, so instances whose totals
  do not fit are excluded. `decimal * int` is limited to the decimal range, as products outside
  `mulRange` are excluded for integers; `mulRange` keeps applying to integer products only.
  `decimal * decimal` and divisions with a decimal are not limited to the decimal range, only to a
  domain Choco accepts: an operand can be the uninitialized ref of a clafer that does not exist,
  beyond the range, and limiting the result forced every such clafer to exist
  (`[ all i : Item | i.ref * 1.5 <= 30 ]`). chocosolver does not warn about sums that may exceed
  the bound.
* **Intermediate values:** the fixed-point propagators compute `x · y` and `x · s` in `long`
  arithmetic, so no intermediate variable exceeds the bound.
* **The uninitialized ref** (`getUninitalizedRef`: `intHigh + 1` for integers) is
  `decimalHigh · s + 1` for decimals, `B + 1 = MAX_INT_BOUND` by default.
* **Search:** a free decimal ref has up to 43 million values; enumerating all instances of
  `x -> decimal` without constraints is as long as that. Bounded constraints
  (`[ x >= 0 && x <= 10 ]`) narrow it, and `--mindecimal`/`--maxdecimal` narrow every decimal ref
  at once.

## Output

`ClaferSolutionMap` decodes a decimal ref to a `BigDecimal` (`BigDecimal.valueOf(v, k)`), so
`InstanceClafer.print` shows `1.99`. Decimals print in the shortest form with at least one
fractional digit (decided Oct 26, 2026): `199.0`, `12.5`, `-0.25`, `0.0`, never `12.50` or
`1.25E+3`. In Java, `stripTrailingZeros().toPlainString()`, adding `.0` when the result has no
point. The fractional digit tells decimals from integers in the output, and the scale does not
show.

## JS format between clafer and chocosolver

New, all in the existing style:

* `decimalScale(k);` with the scope statements (after `stringLength`), emitted when the model has
  decimals or `--decimal-digits` is given, and `decimalRange("low", "high");`, which clafer does
  not emit yet (without it, chocosolver uses the largest range that fits).
* `Decimal`, the type of decimals, like `Int` and `string`: `c.refTo(Decimal)`,
  `c.refToUnique(Decimal)`.
* `decimal("1.99")`, a decimal constant. The literal is a string so that chocosolver reads it
  exactly with `BigDecimal`; a JS number would pass through Rhino as a `double`, and
  `constant(1.99)` today goes to `Asts.constant(int)`.

```
rate -> decimal
[ rate = 1.99 ]

interest -> decimal = 100 * rate
```

becomes

```
defaultScope(1);
stringLength(16);
decimalScale(2);

$rate = Clafer("rate").withCard(1, 1);
$interest = Clafer("interest").withCard(1, 1);
$rate.refToUnique(Decimal);
Constraint(equal(joinRef(global($rate)), decimal("1.99")));
$interest.refToUnique(Decimal);
Constraint(implies(some(global($interest)), equal(joinRef(global($interest)), mul(constant(100), joinRef(global($rate))))));
```

(the same as the int version, with `Decimal`, `decimal(...)` and `decimalScale`). The instance
prints `rate -> 1.99` and `interest -> 199.0`.

## Changes by repository

### clafer

* `Common.hs`: `decimalType` in `primitiveTypes`; a built-in `decimal` clafer whose super is
  `real`, and `integer`'s super becomes `decimal` (it was `double`). `properTargetSubtyping` keeps
  refining a `double` reference to `integer` valid.
* `Intermediate/Intclafer.hs`: `IDecimal`, keeping the literal exactly; the desugarer builds it
  from `PosReal` instead of `IReal`.
* `Intermediate/TypeSystem.hs`, `ResolverType.hs`: `TDecimal`, numeric: `decimal` with `integer`
  is `decimal`; with `double`, there is no common type. A `sum` of decimals is a decimal; a
  `product` of decimals is refused.
* `Clafer.hs`: the Choco-mode check refuses references to `real`/`double` and double literals,
  and allows decimals; Alloy also refuses decimals ("Alloy output unavailable because the model
  contains a decimal").
* `Generator/Choco.hs`: `genTarget "decimal" = "Decimal"`; `IDecimal` emits `decimal("…")` with
  exactly `k` digits; `genScopes` emits `decimalScale` (and `decimalRange` when set); compute `k`
  from the literals.
* `Generator/Alloy.hs` and the other generators: handle `IDecimal` and `TDecimal` like `IReal`.
* `ClaferArgs`: `--decimal-digits` (the largest across the imported files).
* Tests: `test/positive/decimals.cfr` with its regression outputs, and the existing models whose
  decimal literals changed type.
* `doc/CheatSheet.md`: `decimal` with `integer`, `double`, `real` and `string` in the predefined
  sets, the literal rules, and a compatibility table row (Choco: 0.5.5, Alloy: -).

### chocosolver

* AST (`org.clafer.ast`): `AstDecimalClafer` singleton and `Asts.DecimalType`, like
  `AstIntClafer`; `AstDecimalConstant` holding a `BigDecimal`; `Asts.decimal(String)`.
* `scope/Scope`: `decimalScale`, `decimalLow`, `decimalHigh` (and the builder), with the fit check.
* JS: `header.js` (`Decimal`, `decimal`, `decimalScale`, `decimalRange`), `JavascriptContext`
  setters, `JavascriptFile` recording whether the model sets them; CLI options in `cli`.
* `ast/analysis/TypeAnalyzer`: the typing rules above; it lowers decimal expressions to integer
  ones at scale `k` (scaling constants and integers, inserting the fixed-point operations), so the
  later analyses and the IR see only integers. `sum`, `min`, `max` accept refs to decimals.
* The other places that test `AstIntClafer`: `AstCompiler` (`getRefRange`, `getUninitalizedRef`),
  `GlobalCardAnalyzer`, `ProductType`, `Asts`.
* IR and propagators: one IR node, `IrDecimalArithm`, compiled to `PropDecimalMul`/`PropDecimalDiv`
  in `org.clafer.choco.constraint.propagator`, with unit tests against `BigDecimal`
  (`DecimalMulTest`, `DecimalDivTest`).
* Output: see [Output](#output).
* Objectives over decimals optimize the scaled integer; `optimalValues()` in the Java API returns
  the scaled values (documented), the CLI prints the instances as decimals.
* Tests: `DecimalTest` (typing, rounding, ranges, quantifiers, `!=`), and
  `src/test/resources/optimization/decimal_bike.js`, an attributed feature model compiled by clafer;
  the strategy benchmark is unchanged.

### Editors

* clafer-vscode (`syntaxes/clafer.tmLanguage.json`), ClaferToolsST (Sublime Text) and clafer's
  `clafer-mode.el` highlight `decimal` as a primitive type; the numeric literal patterns already
  covered decimals.

### Web tools (ClaferToolsUICommonPlatform, shared by the three tools)

* Decimal refs are numeric like integers (typed `int` in the instance tables), and values are
  parsed with `Number` instead of `parseInt`; `decimal` is a primitive type and highlighted in the
  editors (ace). ClaferMooVisualizer's charts already used `parseFloat`/`Number`.

### Not affected

Alloy (decimals are unsupported there, with clafer's message) and the instance checker in
clafer-semantics (no primitives yet). claferIG refuses such a model with the compiler's reason
instead of crashing.

## Out of scope for the first version

* `product` of refs to decimals; sets of integers compared with sets of decimals.
* Options for the decimal range (`--mindecimal`/`--maxdecimal`) and a warning when a sum may
  exceed it.
* `real` (native real variables, Ibex) and `double` (IEEE 754).
* Per-clafer scales (`cost -> decimal(2)`); one model-wide scale keeps the rules simple.

## Order of work

1. clafer: the `decimal` type, `IDecimal` literals and their typing; tests of the type system.
2. chocosolver: AST type, scope, JS API, typing and lowering for `+ - * /` and comparisons,
   output; Java-API tests.
3. clafer: the Choco generator (`Decimal`, `decimal(...)`, `decimalScale`), the options, the
   backend checks, tests.
4. chocosolver: the fixed-point propagators, `sum`/`min`/`max`, sets, ternary, `%`, ranges and
   their checks, objectives.
5. clafer-vscode, the web tools, the CheatSheet and the changelogs.

## Changes from the draft

The draft of Oct 26, 2026 planned some things differently from what was implemented:

* The range options `--mindecimal`/`--maxdecimal` were not implemented; only the JS
  `decimalRange` narrows the range, and clafer does not emit it.
* The fixed-point IR node and propagators are `IrDecimalArithm`, `PropDecimalMul` and
  `PropDecimalDiv`, not `IrFixedMul`/`IrFixedDiv` and `PropFixedMul`/`PropFixedDiv`.
* Bounded domains apply to every interval domain of more than 2^16 values, not only to decimals.
* Decimal products and divisions are not clamped to the decimal range (uninitialized refs of
  absent clafers lie beyond it), and chocosolver does not warn about sums that may exceed it.
* `decimal` with `double` has no common type, instead of `real`; both backends refuse doubles, so
  the result is the same.
* `IReal` stays in the IR, for a future backend with native real variables.
