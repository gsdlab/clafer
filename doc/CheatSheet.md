# Clafer Cheat Sheet

The cheat sheet is based on the [grammar](https://github.com/gsdlab/clafer/blob/master/src/clafer.cf) and the [generated syntax documentation](https://github.com/gsdlab/clafer/raw/master/doc/clafer.pdf).
The cheat sheet additionally provides commentary and type information, while sacrificing formality of the grammar.

## Predefined sets

### Sets of primitive values

`decimal` is a number with a fixed number of fractional digits, the decimal scale of the model: the most fractional digits of the model's decimal literals, unless given by `--decimal-digits`.
`decimal * decimal` and divisions with a decimal round to the scale, half away from zero (`19.99 * 0.13` is `2.6` with 2 digits); a division of integers stays an integer division (`2 / 3` is `0`).
Equality is exact, after rounding, so a constraint holds only on the grid of the scale: `x * x = 2` has no instance with 2 digits, since `1.41 * 1.41` is `1.99` and `1.42 * 1.42` is `2.02`.
Either use more digits (with `--decimal-digits=4`, `x` is `±1.4142`), or allow a tolerance with two inequalities: `[ x * x >= 1.98 && x * x <= 2.02 ]` gives `x` is `±1.41` and `±1.42`.
Decimals are supported by the Choco backend only.
`double` is a double precision floating point number (not supported by backends).
`real` is an algebraic real (not supported by backends).

Integers are decimals, and decimals and doubles are reals. A decimal and a double have only `real` in common, since most decimals are not doubles (`0.1` is not), so they do not mix.

```
integer
decimal
double
real
string
```

### Set of all clafer instances

```
clafer
```

## Declarations of model elements

### Element

A clafer model consists of clafers, enums, constraints, assertions, optimization objectives, and escapes:

`<element>`:
```
<clafer>
<enum>
<constraint>
<assertion>
<objective>
<Alloy escape>
<ChocoSolver escape>
```

### Clafer

A clafer defines a set of its instances.
Clafer nesting defines the nesting (structure) of instances.
The only mandatory part of clafer declaration is `<name>`:.

`<clafer>`:
```
<abstract?> <temporal modifier*> <group cardinality?> <name> <super?> <reference?> <multiplicity?> <initializer?> <transition?>
    <elements*>
```

An abstract clafer does not have any instances directly, only through concrete clafers extending it.
By default, clafers are concrete (not abstract).

`<abstract>`:
```
abstract
```

Group cardinality restricts the valid number of children of the clafer:
`xor` = `1..1`,
`or` = `1..*`,
`mux` = `0..1`,
`opt` = `0..*`,
or a range `n..m`.
The default group cardinality is `0..*`.

`<group cardinality>`:
```
xor
or
mux
opt
<int literal>..<int literal>
```

A clafer inherits group cardinality, children, and reference of its super clafer.

`<super>`:
```
: <name>
```

Instances of a reference clafer point to instances from the target set expression.
When declared using `->` (set), the instances pointed to cannot repeat per each instance of its parent,
whereas duplicate values are allowed when declared using `->>` (bag).

`<reference>`:
```
-> <set expression>
->> <set expression>
```

The number of instances of a clafer per each instance of its parent is restricted by multiplicity.
The default multiplicity depends on the parent clafer's group cardinality:
if the clafer has no group cardinality (or `0..*`), the default multiplicity is `1`;
for a keyword (`xor`, `or`, `mux`, `opt`) or another range, it is `0..1`.
Useful shorthands are
`?` = `0..1`,
`*` = `0..*`
`+` = `1..*`

`<multiplicity>`:
```
?
*
+
<int literal>
<int literal>..<int literal>
<int literal>..*
```

Reference clafers can be given values using an initializer:
constant using `=` and default using `:=` (no backend currently supports default).

`<initializer>`:
```
= <set expression>
:= <set expression>
```

#### Examples

* We declare two concrete clafers, `B` nested under `A`.
Both have group cardinality `0..*`, , no super, no reference, no initializer, and multiplicity `1`.

```
A
    B
```

* An abstract clafer `A`,
with group cardinality `xor`,
which inherits from `B`,
whose instances can only point to instances from set `C ++ D`,
whose each instance points to a different instance from set `CD`.

```
abstract xor A : B -> C ++ D 1..* = CD
```

### Enum

An enumeration is syntactic sugar to declare an abstract clafer and concrete clafers inheriting from it to represent its literals.

```
enum <name> = <literal> | <...>
```

#### Examples

An enumeration `A` with literals `B`, `C`, and `D`.

```
enum A = B | C | D
```

which is desugared to

```
abstract A
B : A
C : A
D : A
```

### Constraint

Constraint is a boolean expression that we require to be true.

A constraint can be top-level, meaning it must be true for each instance of the model:

```
[ <boolean expression> ]
```

Or nested, meaning it must be true for each instance of the context clafer:

```
<clafer>
    [ <boolean expression> ]
```

A model instance is correct iff all constraints hold.
Constraints are used for instance generation.

### Assertion

An assertion is a boolean expression that we are checking whether it is true for all instances of the model.
A failed assertion means there exists an instance for which the boolean expression is not true.
An assertion can be nested in a clafer; it then holds for each of its instances.
To check the assertions of a model, use the command `check` of claferIG or the button Check of ClaferIDE.
Each failed assertion gives a counterexample.
The check is bounded: no counterexample means that the assertion holds within the scopes and the maximum trace length, not in general.

```
assert [ <boolean expression> ]
```

Assertions are used for verifying universal properties of a model.

### Objective

Objectives guide the instance generation process to minimize or maximize the values of the given numeric expressions.
All objectives in a model are equally important and optimal instances trade a worse value of one objective for an improved value of another one.

Minimize

```
<< minimize <numeric expression> >>
```

Maximize

```
<< maximize <numeric expression> >>
```

## Expressions

### Boolean expressions

These expressions produce either true or false.
There are no true and false literals in the language.

Boolean logic:

`<boolean expression>`:
```
if <boolean expression> then <boolean expression> else <boolean expression>
<boolean expression> <=> <boolean expression>
<boolean expression> => <boolean expression>
<boolean expression> || <boolean expression>
<boolean expression> xor <boolean expression>
<boolean expression> && <boolean expression>
! <boolean expression>
```

Quantified expressions:

Simply quantified:

`lone` means less than one.
`some` means at least one.
`not` is a synonym of `no`.

`<boolean expression>`:
```
lone <set expression>
one <set expression>
some <set expression>
no <set expression>
not <set expression>
```

Quantified with local declarations:

`<boolean expression>`:
```
all disj <local declarations> | <boolean expression>
all <local declarations> | <boolean expression>
one disj <local declarations> | <boolean expression>
one <local declarations> | <boolean expression>
some disj <local declarations> | <boolean expression>
some <local declarations> | <boolean expression>
no disj <local declarations> | <boolean expression>
no <local declarations> | <boolean expression>
```

`<local declarations>`:
```
<name> : <set expression> ; <...>
```

Numeric comparisons:

`<boolean expression>`:
```
<numeric expression> < <numeric expression>
<numeric expression> > <numeric expression>
<numeric expression> <= <numeric expression>
<numeric expression> >= <numeric expression>
```

Overloaded comparisons (can be sets of instances or primitive values):

`<boolean expression>`:
```
<set expression> = <set expression>
<set expression> != <set expression>
<set expression> in <set expression>
<set expression> not in <set expression>
```

### Numeric expressions

`#` computes the set cardinality.

`<numeric expression>`:
```
<int literal>
<decimal literal>          // e.g., 19.99
<double literal>           // e.g., 1.5e-3
<numeric expression> + <numeric expression>
<numeric expression> - <numeric expression>
<numeric expression> * <numeric expression>
<numeric expression> / <numeric expression>
<numeric expression> % <numeric expression>
- <numeric expression>
sum <numeric expression>
product <numeric expression>
# <set expression>
```

### String expressions

`<string expression>`:
```
"<character>*"
```

### Set expressions

Expressions which result in sets.

`.` is relational join.
`,` is a synonym for union `++`.

`<set expression>`:
```
<numeric expression>
<string expression>
<identifier>
if <boolean expression> then <set expression> else <set expression>
<set expression> ++ <set expression>
<set expression> , <set expression>
<set expression> -- <set expression>
<set expression> ** <set expression>
<set expression> . <relation expression>
```

### Relational expressions

`:>` is range restriction.
`<:` is domain restriction.

`<relation expression>`:
```
<identifier>
<relation expression> :> <set expression>
<set expression> <: <relation expression>
```

### Identifiers

`this` is a singleton set referring to an instance of the context clafer.
`parent` is a relation from the context clafer to its parent.
`dref` is a relation from the context reference clafer to its target set.


`<identifier>`:
```
<name>
this
parent
dref
```

## Temporal models

A model with temporal modifiers or operators is dynamic: its instances are traces, sequences of states, each of them an instance of the model.
A trace is a lasso: after the last state, it loops back to an earlier state and repeats from there forever.
A clafer can come and go between the states.
Temporal models are supported by the Alloy backend only.

The behaviour can be written in three styles, which can be mixed.
For a complete model, see the example `CoffeeMachine.cfr` in ClaferIDE.

### Temporal modifiers

`initial` means that the clafer is present in the first state of its parent.
`final` means that the clafer, and its reference, do not change during a trace. Another trace can have other values, so `final` suits the features of a product line.
`finalref` fixes only the reference of the clafer, and `finaltarget` only the set that it points to.

`<temporal modifier>`:
```
initial
final
finalref
finaltarget
```

### Transitions

A transition is a boolean expression that holds whenever its source does.
`a --> b` says that from `a` the next state is `b`, and `a -->> b` that `a` lasts until `b`, however long that takes.
A guard strengthens the source: the transition holds only when the guard also holds.

`<boolean expression>`:
```
<boolean expression> --> <boolean expression>          // a => X b
<boolean expression> -->> <boolean expression>         // a => (this && a) U b
<boolean expression> -[ <guard> ]-> <boolean expression>    // a && g => X b
<boolean expression> -[ <guard> ]->> <boolean expression>   // a && g => (this && a) U b
```

A clafer can declare its own transition, which is a constraint of the clafer.

`<transition>`:
```
--> <boolean expression>
-->> <boolean expression>
-[ <guard> ]-> <boolean expression>
-[ <guard> ]->> <boolean expression>
```

`<guard>`:
```
<boolean expression>
```

A chain is a sequence: `a --> b --> c` is `a => X (b && X c)`.
With `initially`, it is a scenario, which holds once, at the start of the trace.

* A transition says only what happens when it fires: it does not keep the other clafers from changing, and it does not keep the state from changing without it.
* A clafer has one transition. Give a state more ways out with constraints, e.g., `[ a -[ g ]-> c ]`.
* The transition of a nested state disappears when its enclosing state is left.
* A clafer that starts with `xor` cannot follow a transition, because `xor` continues the expression: declare it first, or write the transition as a constraint.

#### Examples

```
final milk ?
coin ?

xor machine
    initial idle -[ coin ]-> brewing
    brewing -[ milk ]->> frothing
    [ brewing -[ no milk ]->> ready ]
    frothing --> ready
    ready --> idle

[ initially (machine.idle --> machine.brewing) ]
```

### Temporal logic

A constraint holds in every state by default, as if it started with `G`: its context is present in that state.
What a constraint requires of later states (`X`, `F`, `G`, `U`) lasts while the parent of its context exists, also after the context itself is gone, e.g., `[ req=down --> movingDown ]` in the state `movingUp` leads to `movingDown`.
To make a constraint last longer, place it higher in the hierarchy, or at the top level.
Use `initially` to anchor a constraint to the first state of its context, which at the top level is the start of the trace, so `[ initially (sometime a) ]` means once, whereas `[ sometime a ]` means again and again.
`finally` anchors a constraint to the last state of its context instance, before it disappears.

Each operator has a symbol and a keyword.

`<boolean expression>`:
```
X <boolean expression>                                 // next
F <boolean expression>                                 // eventually
G <boolean expression>                                 // globally
<boolean expression> U <boolean expression>            // until
<boolean expression> W <boolean expression>            // weakuntil
next <boolean expression>
eventually <boolean expression>
globally <boolean expression>
<boolean expression> until <boolean expression>
<boolean expression> weakuntil <boolean expression>
initially <boolean expression>
finally <boolean expression>
```

### Dwyer's patterns

Specification patterns say what must hold in a part of the trace, without temporal operators: they read as requirements.
A pattern without a scope holds on the whole trace.

`<boolean expression>`:
```
never <boolean expression> <pattern scope?>                                    // absence
sometime <boolean expression> <pattern scope?>                                 // existence
lonce <boolean expression> <pattern scope?>                                    // at most once
always <boolean expression> <pattern scope?>                                   // universality
<boolean expression> must precede <boolean expression> <pattern scope?>        // precedence
<boolean expression> must follow <boolean expression> <pattern scope?>         // response
```

`<pattern scope>`:
```
before <boolean expression>
after <boolean expression>
between <boolean expression> and <boolean expression>
after <boolean expression> until <boolean expression>
```

#### Examples

```
[ never coin between brewing and ready ]
[ ready must follow coin ]
```

### Assertions on traces

An assertion must hold for all traces of the model, up to the maximum trace length, and a failed assertion gives a trace as a counterexample when it is checked.

```
assert [ machine.idle && no coin => X machine.idle ]
```

## Escapes

Escapes allow to write fragments of code in the target language of the clafer compiler: Alloy or ChocoSolver.

### Escape to Alloy

`<Alloy escape>`:
```
[alloy|
<Alloy code>
|]
```

### Escape to ChocoSolver

`<ChocoSolver escape>`:
```
[choco|
<ChocoSolver code>
|]
```

## Compiler options in the model

The first line of a model can give options of the compiler, as on its command line:

```
//# OPTIONS <options>
```

For example, `//# OPTIONS --maxint=1000 --import=design-space.cfr`.
An unknown option is an error.
The command line takes precedence over the options in the model.

### Models in several files

A model can import other models, which are compiled with it as one model (since 0.5.4):

```
//# OPTIONS --import=<file>
```

or on the command line: `clafer SystemA.cfr --import=design-space.cfr`.

* `--import` can be repeated, to import several files. An imported file must be a `.cfr` file.
* A path is relative to the file that imports it (on the command line, to the current directory). A model and its imports can be URLs (`http://`, `https://`); an import in a model read from a URL is relative to that URL, and it can only import URLs.
* The imports are followed transitively. Each file is compiled once, before the files that import it. An import cycle is an error.
* All files share one namespace, as if they were concatenated: a clafer of one file can be used in the others, and the same top-level name in two files is an error.
* The options of all files are combined: the largest `--maxint`, the smallest `--minint`, all modes and imports. The layout (`-l`, `--nl`) must be the same in all files. Options of the compilation (e.g., `-o`, `-s`) are only allowed in the compiled model.
* Errors give the file in which they are: `Compile error at design-space.cfr:12:5`, i.e., file, line and column.
* `-v`, `--tooldir` and the options that restrict the imports (`--import-root`, `--public-imports`, `--import-base`) can only be given on the command line.

# Backend Compatibility

The following table provides versions in which support for a given feature was added to Alloy-based and Choco-based backend.

<table>

<tr>
<th>Language Feature</th><th>Alloy</th><th>Choco</th>
</tr>

<tr>
<td>Nested abstract clafers</td>
<td>0.3.9</td>
<td>0.4.3</td>
</tr>

<tr>
<td><code>assert [ ... ]</code></td>
<td>0.3.9</td>
<td>0.4.2</td>
</tr>

<tr>
<td><code>product</code></td>
<td>&nbsp;&nbsp;&nbsp;-</td>
<td>0.3.9</td>
</tr>

<tr>
<td>Modulo division <code>%</code></td>
<td>0.3.9</td>
<td>0.4.2</td>
</tr>

<tr>
<td>Group cardinality inheritance</td>
<td>0.3.9</td>
<td>0.4.2</td>
</tr>

<tr>
<td>Reference refinement and redefinition</td>
<td>0.4.0</td>
<td>0.4.4</td>
</tr>

<tr>
<td>Escapes (<code>[alloy| ... |]</code> and <code>[choco| ... |]</code>), <code>dref</code>, and <code>**</code></td>
<td>0.4.1</td>
<td>0.4.1</td>
</tr>

<tr>
<td><code>min</code> and <code>max</code></td>
<td>0.4.3</td>
<td>0.4.2</td>
</tr>

<tr>
<td><code>&lt;:</code> and <code>:&gt;</code></td>
<td>0.3.0</td>
<td>0.4.2</td>
</tr>

<tr>
<td><code>decimal</code></td>
<td>&nbsp;&nbsp;&nbsp;-</td>
<td>0.5.5</td>
</tr>

<tr>
<td>Temporal models</td>
<td>0.5.6</td>
<td>&nbsp;&nbsp;&nbsp;-</td>
</tr>

<tr>
<td><code>double</code>, <code>real</code></td>
<td>&nbsp;&nbsp;&nbsp;-</td>
<td>&nbsp;&nbsp;&nbsp;-</td>
</tr>

<tr>
<td>Default initializer <code>:=</code></td>
<td>&nbsp;&nbsp;&nbsp;-</td>
<td>&nbsp;&nbsp;&nbsp;-</td>
</tr>

<tr>
<td>Models in several files (<code>--import</code>)</td>
<td>0.5.4</td>
<td>0.5.4</td>
</tr>

</table>
