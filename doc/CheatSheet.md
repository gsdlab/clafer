# Clafer Cheat Sheet

## Predefined sets

### Sets of primitive values

`double` is a double precision floating point number (limited support by ChocoSolver backend).
`real` is an algebraic real (not supported by backends)

```
integer
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

`<element>`
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
The only mandatory part of clafer declaration is `<name>`.

`<clafer>`
```
<abstract?> <group cardinality?> <name> <super?> <reference?> <multiplicity?> <initializer?>
    <elements?>
```

An abstract clafer does not have any instances directly, only through concrete clafers extending it.
By default, clafers are concrete (not abstract).

`<abstract>`
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

`<group cardinality>`
```
xor
or
mux
opt
<lower bound>..<upper bound>
```

A clafer inherits group cardinality, children, and reference of its super clafer.

`<super>`
```
: <name>
```

Instances of a reference clafer point to instances from the target set expression.
When declared using `->` (set), the instances pointed to cannot repeat per each instance of its parent,
whereas duplicate values are allowed when declared using `->>` (bag).

`<reference>`
```
-> <set expression>
->> <set expression>
```

The number of instances of a clafer per each instance of its parent is restricted by multiplicity.
The default multiplicity depends on the parent clafer's group cardinality:
if the group is `0..*` then the default multiplicity is `1`, otherwise it is `0..1`.
Useful shorthands are
`?` = `0..1`,
`*` = `0..*`
`+` = `1..*`

`<multiplicity>`
```
?
*
+
<number>
<number>..<number>
<number>..*
```

Reference clafers can be given values using an initializer:
constant using `=` and default using `:=` (no backend currently supports default).

`<initializer>`
```
= <set expression>
:= <set expression>
```

#### Examples

We declare two concrete clafers, `B` nested under `A`.

```
A
    B
```

An abstract clafer `A`, with group cardinality `xor`, which inherits from `B`, whose instances point to instances of type `C` from the set `C2`.

A concrete clafer `D`, which is nested under `A`, with multiplicity `?`, and no group cardinality, no super, no reference, no initializer, and no children.

```
abstract xor A : B -> C ++ D 1..* = C2
    D ?
```

### Enum

An enumeration is a syntactic sugar to declare an abstract clafer and concrete clafers inheriting from it to represent its literals.

```
enum <name> = <literal> | <...>
```

#### Examples

An enumeration `A` with literals `B`, `C`, and `D`.

```
enum A = B | C | D
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

```
assert [ <boolean expression> ]
```

Assertions are used for verifying universal properties of a model.

### Objective

Objectives guide the instance generation process to minimize or maximize the values of the given numeric expressions.
All objectives in a model are equally important and optimal instances trade a worse value of one objective for an improved value of another one.

Minimize

```
<< min <numeric expression> >>
```

Maximize

```
<< max <numeric expression> >>
```

## Expressions

### Boolean expressions

These expressions produce either true or false.

Boolean logic:

`<boolean expression>`
```
if <boolean expression> then <expression> else <expression>
<boolean expression> <=> <boolean expression>
<boolean expression> => <boolean expression>
<boolean expression> || <boolean expression>
<boolean expression> xor <boolean expression>
<boolean expression> && <boolean expression>
! <boolean expression>
```

Quantified expressions:

Simply quantified:

`some` means at least one instance in the set.
`not` is a synonym to `no`.

`<boolean expression>`
```
one <set expression>
some <set expression>
no <set expression>
not <set expression>
```

Quantified with local declarations:

`<boolean expression>`
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

`<local declarations>`
```
<name> : <set expression> ; <name> : <set expression> <...>
```

Numeric comparisons:

`<boolean expression>`
```
<numeric expression> < <numeric expression>
<numeric expression> > <numeric expression>
<numeric expression> <= <numeric expression>
<numeric expression> >= <numeric expression>
```

Overloaded comparisons (can be sets of instances or primitive values):

`<boolean expression>`
```
<set expression> = <set expression>
<set expression> != <set expression>
<set expression> in <set expression>
<set expression> not in <set expression>
```

### Numeric expressions

`<numeric expression>`
```
<literal>
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

### Set expressions

`,` is a synonym for union `++`.

`<set expression>`
```
<set expression> ++ <set expression>
<set expression> , <set expression>
<set expression> -- <set expression>
<set expression> ** <set expression>
<set expression> . <relation expression>
```

### Relational expressions

`<relation expression>`
```
<set expression> :> <set expression>
<set expression> <: <set expression>
```

## Escapes

Escapes allow to write fragments of code in the target language of the clafer compiler: Alloy or ChocoSolver.

### Escape to Alloy

`<Alloy escape>`
```
[alloy|
<Alloy code>
|]
```

### Escape to ChocoSolver

`<ChocoSolver escape>`
```
[choco|
<ChocoSolver code>
|]
```
