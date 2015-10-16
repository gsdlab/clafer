# Clafer Cheat Sheet

The cheat sheet is based on the [grammar](https://github.com/gsdlab/clafer/blob/develop/src/clafer.cf) and the [generated syntax documentation](https://github.com/gsdlab/clafer/raw/master/doc/clafer.pdf).
The cheat sheet additionally provides commentary and type information, while sacrificing formality of the grammar.

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
<abstract?> <group cardinality?> <name> <super?> <reference?> <multiplicity?> <initializer?>
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
if the group is `0..*` then the default multiplicity is `1`, otherwise it is `0..1`.
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
<double literal>
<real literal>
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
<set expression> <: <set relation>
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
