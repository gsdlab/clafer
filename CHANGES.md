##### Clafer Version 0.5.8, unreleased

* Builds with GHC 9.12.4 (Stackage nightly-2026-11-11) and still with GHC 9.6.7. The lexer is generated with alex 3.5: the lexer generated in 2018 did not compile with GHC 9.12 (`Int#` instead of `Int16#`).
* No longer depends on `data-stringmap`, which is not maintained and does not build with GHC 9.6 or later from Hackage: the maps of UIDs are `Data.Map` maps. The outputs are the same (the positive test models and the case studies), and compiling is as fast.
* No longer depends on `json-builder`, which is not maintained and does not build from Hackage with GHC 8.4 or later: the `.cfr-map` and `.cfr-scope` files are written with `aeson`'s encoding, field by field in the same order. The files of the positive test models (Alloy and Choco modes) are the same.
* Depends only on the packages it uses: `cond`, `executable-path`, `mtl-compat`, `parsec` and `transformers-compat` are no longer dependencies of the library, and `HUnit`, `QuickCheck` and `lens-aeson` no longer of the test suites.
* The initializer `:=` is the initial value of a reference ([kbak/clafer-semantics#164](https://github.com/kbak/clafer-semantics/issues/164), `doc/initial-value.md`, errata T14). It compiled to an assertion in every output ([#116](https://github.com/gsdlab/clafer/issues/116)), so `x -> integer := 10` with `[ x = 5 ]` had instances and a counterexample; it is a hard constraint now, and has no instance there.
  * In a static model, `:=` is the same as `=`: `[ some x => x.dref = 10 ]` in the parent's context. The outputs are the same as with `=`, and an initializer does not make a model temporal.
  * In a temporal model, every lifetime of `x` starts with the value, which may change afterwards: `[ initially this.dref = 10 ]` in the context of `x`. The value is resolved in the parent's context, where it is written: `this` is the parent, and a name `y` is the sibling `y` of `x` even if `x` has a child `y`.
  * A set initializer, e.g., `xs -> integer * := 1, 2`, stays in the parent's context: `[ initially (some xs => xs.dref = 1, 2) ]`. The instances created later are not initialized.
  * The reference of a `final` or `finalref` clafer cannot change, so `:=` is `=` there.
  * Redefining an inherited `:=` in a subclafer is open; an own initializer is added to the inherited one.
  * New test models: `initialValueStatic` (the same instances as with `=` in claferIG and chocosolver), `tmp_initialValue01` (an optional `level` created later), `tmp_initialValue02` (a mandatory `x` whose value changes), `tmp_initialValue03` (a parent that is replaced), `tmp_initialValue04` (`finalref` and `final`), `tmp_initialValue05` (set initializers), `tmp_initialValue06` (the name resolution and an abstract clafer), and the test case `InitialValue`.
* `let v = e in body` compiles ([#114](https://github.com/gsdlab/clafer/issues/114)): it is `body` with `e` for `v`. It crashed the compiler in every mode ("pattern expressions should have been transformed previously"). The bound expression may be any expression above `in`, e.g., `let s = a + b in s > 2` or `let w = A.v in w = 3`; it could only be a name. A quantifier or a `let` in `body` that binds `v` again hides it, and one that binds a name used in `e` is renamed (`x_1`), so that `e` keeps its meaning. New test model: `let_binding`.
* An ambiguous name of a super, e.g., `x : T` with `A.T` and `B.T`, is an error that the name is not unique, with the paths of the candidates (`A.A__T`, `B.B__T`), as for a reference ([#115](https://github.com/gsdlab/clafer/issues/115)). It was reported as a duplicate definition, with the UIDs. Two supers with the same name in the same namespace are still a duplicate definition. New negative test model `ambiguous_super_name` and the test case `AmbiguousSuperName`.

##### Clafer Version 0.5.7, Nov 8, 2026

* The UID of a clafer is its least-partially-qualified name, with `__` between the names: `size` if no other clafer is named `size`, `x__size` for the `size` in `x` otherwise, and `root__size` for a top-level `size` that is the end of another clafer's path. It was `c0_size`, `c1_size`, ..., numbered in the order of the model, for every clafer, so a UID changed when a clafer with the same name was added before it, and tools cut the prefix off to show the name (which also cut `abc_def` to `def`). The UIDs are the names in all outputs: the Alloy signatures, the Choco model, the explicit model, the JSON IR, the HTML anchors and the scope files. An apostrophe is `_prime` (`a'` is `a_prime`; it was `c0_a__prime__`), and a UID that would be the same as one before it in the model gets `__2`, `__3`, ... (e.g., `a_prime` next to `a'`, or a copy of an inherited clafer with `-i`).
  * A UID is also the least-partially-qualified name in the `.cfr-map` and the scope files; the fully qualified name is `root__x__size` (it was `::x::size`). A lookup by name takes a UID or a qualified name with `__`, and the older form with `::`.
  * The outputs write the UIDs in the form their language allows: the Alloy output renames a clafer whose UID is an Alloy keyword (e.g., `sig`), a function of `util/integer` (e.g., `max`) or a name the generators write (e.g., `show`), or whose relation or reference names clash with another clafer's (`r_x` next to `x`), to the first free `sig_1`, `sig_2`, ...; the variables of the Choco output are `$` and the UID (`$x__size = $x.addChild("x__size")`), and those of the locals of quantifiers `$_` and the name, so that a clafer named, e.g., `join` or `global`, or a local with the name of a clafer, does not replace them.
  * A name with `__` is a warning in a full model, with its position, since `__` separates the names of a UID; in an explicit model (`-f`, `--explicit`) it is expected.
  * The HTML and graph outputs take the names of the clafers from the model, not from their UIDs.
* A reference to a clafer that extends the referencing abstract clafer, e.g., `abstract Person -> Bob` with `Bob : Person`, no longer makes the compiler loop with `-f` (since the names became the UIDs with `-f` in this release): the walk through the supers and references ends at a clafer that is already on its path.
* A reference to a union of targets with a nested clafer, e.g., `u -> Hub.p ++ fast`, has valid Alloy output: the field is declared over the union of their signatures (`p + fast`), as it is for one target. Alloy refused the path in the declaration (`The name "@r_p" cannot be found`), in static and temporal models; the explicit model keeps the targets as a constraint (`[this.dref in (Hub.p ++ fast)]`).
* Temporal models: the obligations of a constraint (`X`, `F`, `G`, `U`) last while the parent of its context instance exists, not only while the context instance exists ([#107](https://github.com/gsdlab/clafer/issues/107)). A transition nested in its source state, e.g., `[ req=down --> movingDown ]` in the state `movingUp`, as in the power window of Juodisius et al. (2019), takes the machine to `movingDown`; it only forced leaving `movingUp`. The pending obligations of nested states still lapse when their enclosing state is left, and `[ X no this ]` makes an instance last one step. For a top-level clafer, whose parent is the root, they last for the whole trace.
* The transition of a clafer, e.g., `on --> off`, is a constraint of the clafer, with the same meaning as before. For `-->>`, the source lasts until the target holds, while its parent exists.
* Temporal models: a negated obligation lapses with the parent too ([#110](https://github.com/gsdlab/clafer/issues/110)). The negations are pushed inside the temporal operators first, with the dualities of LTL: `!F a` is `G !a`, `!X a` is `X !a`, and `!(a U b)` is `!b W (!a && !b)`. So `[ !(F error) ]` lets the parent disappear, like `[ G !error ]`; it required the parent to exist forever. A formula and its negation may both hold, on a lifetime that ends before their obligations are due. This also applies to the negated parts of the patterns, e.g., `F r` in the scope `between q and r` holds only when `r` occurs while the parent exists. `finally` is an operator of its own, with the same meaning.
* Temporal models: a top-level constraint or assertion holds for `root`, without a variable that Alloy warns about (`all self_ : root | ...` left `self_` unused: "This variable is unused", which claferIG shows as a relevance warning, e.g., for the CoffeeMachine example). No temporal test model or example has an Alloy warning; before, 27 of the test models had one.
* The CheatSheet and the comments of the temporal generator say that a scope bounds the instances of a clafer over the whole trace, not in each state, and that an instance keeps its parent across its absences; a second way out of a state is a constraint in the state, which has the lifetime of the state's own transition ([#111](https://github.com/gsdlab/clafer/issues/111)). New test models: a transition in a final machine and in a replaceable one, negated obligations, the identities in a scope, and the parent of a reappearing instance.
* The names after an explicit `dref` are the children of the reference's target ([#108](https://github.com/gsdlab/clafer/issues/108)): `this.dref.speed`, `dref.speed` and `all t : this.dref | t.speed = 3` compile, and mean the target's `speed`, also when the reference clafer has a child `speed` of its own. They did not compile, since at least 0.5.2 ("Cannot deref from type", or an ambiguous name when the target was a reference too): the name was resolved through the reference a second time.
* A comparison (`=`, `!=`, `in`, `not in`), an intersection (`**`) or a difference (`--`) of two navigations to reference clafers is of their targets ([#87](https://github.com/gsdlab/clafer/issues/87)): `this.a = parent.b.a` is `this.a.dref = parent.b.a.dref`. It compared the instances of `a`, which are never the same under different parents, so such a constraint made a model inconsistent, or held trivially when negated. An operand that is `this`, a variable or ends with `dref` is taken as written, e.g., `this in b.a` in `sel -> b.a`.
* `parent` of an instance of a top-level clafer is the synthetic `root` ([#112](https://github.com/gsdlab/clafer/issues/112)): in a top-level clafer `b`, `parent.a` and `this.parent.a` are `root.a`, i.e., `a`. They compiled to Alloy that refers to the missing relation `@r_c0_b`, and failed in chocosolver with "Cannot join c0_b . parent". The root has no instance in the outputs: `some root`, `one root` and `lone root` hold, `no root` does not, `#root` is 1, and other uses of `root` as a value are refused; `[ some root ]` compiled to an undefined `root`. The parent of a set of instances, e.g., `a.parent` for `a ?`, is the root when an instance exists and empty otherwise: `some a.parent` is `some a`, `#a.parent` is 1 or 0, and `a.parent.c` is `c` when `a` exists.
  * New negative test models for the refused uses: `root_in_union`, `variable_over_root`, `root_as_child`, `compare_root_with_clafer` and `parent_of_optional_top_level`. `doc/root.md` records why the static outputs have no root while the temporal output has a root signature, and what either alternative would cost.
* In a top-level abstract clafer whose subclafers are at the top level and nested, a constraint on the parent of `this` is split on `this`: for the instances of the top-level subclafers, the parent is the root, and for each nested subclafer, the parent of its instances. With `abstract Feat [ some parent ]`, `f1 : Feat` and `g` with `f2 : Feat`, `f1` had no parent in Alloy, so the model had no instances, and chocosolver refused the model; both give the instance now. The parent of a variable of such a clafer is refused. Temporal models already gave the top-level subclafers the root as their parent.
* `root.a` in a temporal model is the top-level clafer `a`; it was the relation from the root to `a`, e.g., in `root.a.x = 2`.
* Temporal models: `final`, `finalref` and `finaltarget` on a clafer that inherits its reference fix the reference ([#109](https://github.com/gsdlab/clafer/issues/109)), e.g., `final motor : engine` under `abstract engine -> Engine`. They fixed only a reference that the clafer declares, so the motor could point to another engine later in the trace; `finalref` and `finaltarget` without a reference of the clafer's own were ignored. A reference modifier after another modifier, e.g., `initial final x -> T`, is no longer ignored either.
* Temporal models: `finaltarget` fixes the set of targets of a clafer's instances while their parent exists, so the instances may change and swap their targets, but a new instance points to one of the targets; `finalref` fixes the reference of each instance while it exists, and `final` both ([kbak/clafer-semantics#127](https://github.com/kbak/clafer-semantics/issues/127)). `finaltarget` fixed the reference of each instance, as `finalref` does. A clafer keeps all its reference modifiers, so `finalref finaltarget x -> T` means both, in either order; only the first one was kept.
* Temporal models: `s must follow p between q and r` requires an `s` before `r` for each `p` up to `r`; it checked only a `p` in the state of `q`, since the brackets of Dwyer's formula were misplaced. `s must precede p after q` starts at the first `q`; Dwyer's formula could start at a later `q`, so q, p, q, s held. At the top level, where a pattern holds in every state, each `q` starts a scope ([kbak/clafer-semantics#127](https://github.com/kbak/clafer-semantics/issues/127)).
* The test model `tmp_TLSHandshakeProtocol_distributed.cfr`, the TLS 1.2 handshake, has traces; it had none since 0.5.0. It mixed tabs and spaces, so most states were nested in the wrong clafers; its versions were compared as instances (#87), and a client and a server agree on a version when they have one in common; the transitions that leave a phase are constraints of the channel, and a phase is left only from its last states; a fatal alert ends the connection; and the server's Finished message no longer contradicts its phase. Its scenarios: a full handshake of 10 states (12 with client authentication), no data before the server's Finished, and a fatal alert when the versions do not overlap.
* Temporal models: a name that resolves through a reference, e.g., `this.speed` in `l -> Port`, compiles to valid Alloy; it joined the target with the set of all existing `speed`s.
* `make test` fails when a test suite fails, or when an output of the positive test models differs from its regression, has no regression, or a regression has no output; the outputs become the new regressions, to be reviewed and committed. It passed regardless, so the regressions of 0.5.6 were outdated.
  * `make test` compiles and validates the positive test models in parallel, one model per core (`make test JOBS=4` for 4 at a time); the messages of each model are printed together. The positive suite takes 75 seconds on 32 threads.
  * The outputs are compared with their regressions exactly; whitespace and blank lines were ignored, so, e.g., a change of the spacing in the explicit models passed unnoticed.
  * `make test` also fails when a positive test model does not compile or one of its outputs does not validate, and names those models after compiling all of them. It printed the errors and passed, e.g., with the Alloy output of `explicit_dref_navigation`, which Alloy refused.
  * `clafer -v` exits with 1 when a tool rejects an output: Alloy, chocosolver, dot, or clafer itself, for the explicit model, which must compile to itself. A counterexample is not a failure. It printed the error and exited with 0, and did not check the explicit model.
* Temporal models: `parent` of an instance of a top-level abstract clafer, and its constraints' obligations, use the parents of its subclafers' instances; `parent` was empty for the instances of a nested subclafer, so `[ some this.parent ]` in `abstract Port` excluded them.
* An abstract clafer that no concrete clafer inherits from, directly or through other abstract clafers, and the clafers in it have the scope 0. With `--keep-unused`, as in claferIG, Alloy gave such a clafer atoms of its own, which its constraints were translated for, and which references could point to; e.g., the power window with three abstract variants of its controller took 223 s for its first trace, and takes 2 s. `emptyAbstracts` in `ScopeAnalysis` gives these clafers.
* The simple scope analysis no longer adds the instances of a clafer that has none, e.g., such an abstract clafer, to the scope of its super: every subclafer added at least 1. The scopes of the supers are smaller, e.g., `WaitingLine` 2 instead of 4 and `participants` 4 instead of 8 in the tutorial, and the `Element` of the UML class diagram model 4 instead of 25.
* Temporal models leave out the abstract clafers that the optimizer removed, as static models do; the temporal generator took the clafers of the model before the optimization.
* The unused JavaCC grammar `src/Language/Clafer/Front/Clafer.jj` is removed. It dated from 2012, was never part of the compiler, and did not follow the syntax since 0.4; the grammar is `src/clafer.cf`.
* Scope files (`.cfr-scope`, claferIG's `loadScopes`): entries other than `{"lpqName": name, "scope": n}`, e.g., chocosolver's `{"int": [-8, 7]}` or `{"defaultScope": 1}`, are skipped; they stopped claferIG with an error. A name may also be a clafer's UID, e.g., `Component__Cfeatures`, as chocosolver writes them.
* Explicit models: a model with everything written out, e.g., as chocosolver's `AstPrinter` prints one, is a Clafer model that compiles to itself with `clafer -f -k -l --ss=none`: all 131 positive test models with a Choco output, printed that way, compile to the same model and give the same instances.
  * `-f` (`--skip-resolver`) means that the names of the clafers are their UIDs: they are not renamed, and they are still resolved and checked, so a misspelled name is an error. It was ignored for models with inheritance, which were renamed (`c0_A` became `c0_c0_A`), and without inheritance it skipped the name resolution and its checks. A name that cannot be a UID, of several clafers or with an apostrophe, is an error with `-f`; `-f` was ignored then too.
  * The Choco output of a nested assertion is quantified over the instances of its clafer, e.g., `assert [ age >= 0 ]` in `abstract P` is `all this_ : P | this_.age >= 0`. It was an assertion over `this` without a context, which chocosolver's validation (`-v`) refused with a type error.
  * A navigation from an intersection or a difference of sets, e.g., `(this ** g.f2).parent`, resolves: from the right operand of `**` and the left of `--`, which contain the set. The split constraints of #112 are of this form.
  * `-m clafer` prints the explicit model of a static model: what chocosolver solves, with every name a UID, every card and group card (inherited ones too), `this`, `parent` and `dref` written out, nested assertions quantified over their clafer, nesting in braces, and the objectives and assertions at the end. With `--meta-data`, its scope file (`model.des.cfr-scope`) has every scope: each clafer's by its UID, the default scope and the ranges of integers, strings and decimals. It printed the desugared model, which was not Clafer: elements ran together on one line (`assert [...]assert [...]abstract ...`). The JavaScript and the explicit model are printed from one walk over the model, so they are the same model: for all 132 positive test models with a Choco output, the explicit model is the one chocosolver prints for the `.js` (for 18, up to the order of abstract and concrete siblings that the solver does not see), with the same scope file, it compiles to itself, and chocosolver gives the same instances for it as for the `.js`. Models with reals have no explicit model yet: `-m clafer` prints nothing for them (it printed their desugared model).
  * `-m clafer` prints the explicit model of a temporal model too, e.g., in ClaferIDE for the temporal CoffeeMachine example, where it showed nothing. It has the temporal modifiers (`initial`, `final`, `finalref`, `finaltarget`) on the clafers, the temporal operators (`F`, `G`, `X`, `U`, `W`, `initially`, `finally`), the patterns and the transitions as the formulas they stand for (`a --> b` in `a` is `[((#this) >= 1) => (X ((#this.parent.b) >= 1))]`), and the trace length among the options (`//# OPTIONS --explicit --tl=10`). chocosolver does not solve it, and Alloy does: all 64 temporal positive test models compile to themselves, and with the original's scopes, Alloy finds as many traces (up to 20) and counterexamples for the explicit model as for the original.
  * A nested assertion is quantified over the instances of its clafer by the path from its top-level clafer, as clafer resolves the name, e.g., `all this_ : machine . ctx | ...` for an assertion in `ctx` in `machine`: with `ctx`, the explicit model did not compile to itself.
  * `--explicit` marks an explicit model: a shorthand for `-f -k -l --ss=none`. An explicit model starts with `//# OPTIONS --explicit`, which `-m clafer` writes, so it needs no options and any file name; chocosolver reads such a model with its own parser, without the compiler.
* `--meta-data` no longer hangs on a model with a single clafer: the search for its least-partially-qualified name did not end.
* `noclafer`, the empty set: no instance of any clafer ([kbak/clafer-semantics#134](https://github.com/kbak/clafer-semantics/issues/134)). Its type is below every clafer type, so `a ++ noclafer` and `if c then a else noclafer` have the type of `a`. Like `root`, it is a reserved name and never declared. The root handling of #112 writes it for a navigation from the parent of an optional top-level clafer (`if some extra then a else noclafer`), where it wrote `a -- a`. Alloy gets `none`; Choco gets an empty constant of the clafer of the set beside it, e.g., `constant($a)`, or of the model's first clafer. A navigation from it, e.g., `noclafer.d` or `noclafer.parent`, is `noclafer`, whatever it navigates to, with a warning. The test model `noclafer.cfr` asserts its laws, which Alloy 6.2 and chocosolver both check.
* A comparison, a difference or an intersection of an expression with itself, e.g., `[ a = a ]` or `noclafer = noclafer`, is a warning, with its position and what it means (always true, always false, always empty, or the expression itself); it was an error, so a correct model did not compile. The warnings are printed with the statistics, like those about large scopes.
* `clafer` as a value: the set of all instances of all clafers, the root excluded, i.e., the union of the clafers with no super clafer, nested ones by their paths (`Thing ++ c ++ c.d`). Static models only; temporal models refuse it.

##### Clafer Version 0.5.6, Nov 1, 2026

* The Alloy outputs have the nested assertions too, for each instance of their clafer, and name the assertions by their line and column (`assertAt_3_5`), so that a line can have several assertions. Nested assertions were ignored, silently in temporal models.
* Temporal models (behavioural Clafer) compile to the temporal logic of Alloy 6: mutable relations (`var`) and the operators `always`, `after`, `eventually` and `until`. The temporal generator encoded traces explicitly for Alloy 4.2, which had no temporal operators, and its output did not compile with Alloy 6. The Alloy Analyzer 6.2 finds the traces of small temporal models and checks their assertions in seconds.
* The semantics of temporal models follows Juodisius et al., *Clafer: Lightweight Modeling of Structure, Behaviour, and Variability* (2019), sections 5 and 6: `a --> b` is `a => X b`, `a -->> b` is `a => (this && a) U b`, and a guard strengthens the precondition (`a -[g]-> b` is `a && g => X b`). It differs from the paper in these points:
  * An instance may disappear and reappear, which cyclic state machines need in the lasso traces of Alloy.
  * The temporal obligations of a constraint (`X`, `F`, `G`, `U`) hold while its context instance exists; a constraint placed higher in the hierarchy, or at the top level, lasts longer.
  * The transition of a clafer, e.g., `on --> off`, is a constraint of its parent, so the transition of a nested state disappears when its enclosing state is left.
  * A chain of transitions is a sequence: `a --> b --> c` is `a => X (b && X c)` (it was `a => X (b => X c)`), e.g., the scenario `[ initially (green --> yellow --> red) ]`. Its first state is a condition, so a scenario states it when the model does not force it.
* Unsat cores of temporal models: the constraints and the cardinalities of the children are facts of their own in the Alloy output, for which Alloy gives the unsat core, so that claferIG can show the constraints that contradict each other; Alloy gives the core of the temporal formulas of a signature fact for the whole fact. The constraint of a clafer transition spans the clafer and its transition, e.g., `green --> yellow`.
* Enumerations are final in dynamic models: their literals do not change over time ([#92](https://github.com/gsdlab/clafer/issues/92)). In static models, they are not final, so that they do not make the model dynamic.
* The parent of a quantified variable, e.g., `[ all b1 : b | b1.parent = a ]`, is the parent of its clafer; it was taken from the context of the constraint, and the compiler failed with "Prelude.head: empty list".
* Partially qualified names match whole names: `yellow` matched `yellow_on` and `yellow_off` too, so it was ambiguous, and its least-partially-qualified name, e.g., in a `.cfr-scope` file, was qualified more than needed (`normal::yellow`).
* HTML and graph outputs: expressions are shown with the parentheses that the grammar requires, e.g., `[ (1 + 2) * 3 = 9 ]` and `X (a || b)`, which were shown as `[ 1 + 2 * 3 = 9 ]` and `X a || b`. `X` was shown as `F`, and the guarded arrows `-[g]->` and `-[g]->>` as `-[g]-->` and `-[g]-->>`.
* The temporal test models are fixed according to the paper and the above changes, the traffic light models are split into one file per model and its scenarios, which import it, and the test suite compiles each model with the models it imports.

##### Clafer Version 0.5.5, Oct 27, 2026

* Decimals: a primitive type `decimal` of numbers with a fixed number of fractional digits, the decimal scale of the model, for the Choco backend (chocosolver 0.5.5). A plain decimal literal, e.g., `19.99`, is a decimal (it was a `real`); the scale is the most fractional digits of the literals, as written, or `--decimal-digits`. `decimal * decimal` and divisions with a decimal round half away from zero; a division of integers stays an integer division. Integers are decimals, decimals and doubles are reals, and a decimal and a double do not mix. `real` and `double` stay unsupported by the backends, and the Alloy backend does not support decimals. In the Choco output: `refTo(Decimal)`, `decimal("19.99")` and `decimalScale(2)`.
* `clafer-mode.el` highlights `decimal` as a type.
* Scopes: a reference with an unbounded multiplicity (`-> Feature *`) gets the scope of its target per parent, as intended; the target's scope was read before it was computed, so it could be 1 or a partial sum of the target's subclafers. Models whose references needed more targets than that had no instances, e.g., ClaferCaseStudies' `AADL_Complete.cfr`.
* Scopes: in the Alloy and Choco modes, the statistics warn about such references whose scope is above 100 and suggest an upper bound, e.g., `Warning: model.cfr:16:5: the scope of Cfeatures -> Feature 0..* is 1672, since Cfeatures may point to all 76 Feature in each of its parents. If fewer suffice, give it an upper bound, e.g., Cfeatures -> Feature 0..10, to make the instance generation faster.`

##### Clafer Version 0.5.4, Oct 25, 2026

* Models in several files: `--import=FILE`, in `//# OPTIONS` or on the command line, compiles the model together with the imported files, transitively, each file once and before the files importing it ([#100](https://github.com/gsdlab/clafer/issues/100)). The options of all files are combined. The model and its imports can be URLs; an import is relative to the importing file's folder or URL.
* Errors give their position as `file.cfr:line:column`, also in a model of one file (`Parse failed at model.cfr:3:5...`, previously `line 3 column 5`), and in a model with imports, the file in which they are. A model read from the standard input is `<stdin>`.
* A syntax error's message no longer repeats the line (`syntax error before ? }`), which in a model with imports was a line of the complete model; the position is given with the error.
* Restricted imports, for models that may come from anyone (e.g., in a web tool): `--import-root=DIR` allows local imports only inside the given folders, after resolving `..` and symbolic links; `--public-imports` allows URL imports only from public addresses (not loopback, private, or link-local ones), checked when connecting, also after a redirect; `--import-base=URL` resolves the imports of a model whose text was read from a URL. These options, `-v`, and `--tooldir` can only be given on the command line, not in `//# OPTIONS`. Downloads are limited to 16 MB.
* An imported file must be a `.cfr` file: a URL's path must end with `.cfr`, also after a redirect, and a URL served as HTML, JSON or XML is refused, so that a model cannot read other files or web pages.
* Models read from URLs: `https://` works (it was read as a local file name), outputs are named after the URL's last segment, in the current directory, and `ftp://` is no longer supported. The compiler uses http-client instead of the HTTP package.
* `//# OPTIONS`: an unknown option or a malformed directive is an error; the whole directive used to be ignored silently. When compiling with the `clafer` executable, a directive with `-m` or with an option's short or custom name (e.g., `-k`, `--check-afm`, `--nl`) was ignored entirely, and `--tl` and `--tooldir` in the directive were overridden by the defaults.
* Clafer names with apostrophes (`same'`) work with Alloy and Choco: an apostrophe is not allowed in their identifiers (in Alloy 6, it is the next-state operator), so it becomes `__prime__` in the clafer's UID (`c0_same__prime__`); the name keeps it. Such models are not counted as able to skip the name resolver.
* `opt` makes the children optional again, as in the language's definition: a child without a multiplicity is optional (`0..1`) under a keyword group (`xor`, `or`, `mux`, `opt`). Since 0.3.3, the default depended only on the interval, and `opt`, being `0..*` like no group at all, made its children mandatory. Only the keywords set `_isKeyword` in the IR, no longer the ranges `0..n`. Children of other ranges are optional and children of no group or `0..*` are mandatory, as before.
* A group cardinality whose lower bound the children cannot reach is a compile error, e.g., `xor` or `or` over no children, or `3..*` over two optional children. The children include the inherited ones, and the group cardinality may be inherited or redefined (`2..2 myGroup : SuperGroup`). Such groups were not constrained in the Alloy and Choco output. An abstract clafer's group is not checked, since its subclafers may add children.
* Layout: comments do not count in the indentation. A line which starts with a comment (`/*history*/ xor on`) is indented as if the comment was not there, at the column where the comment starts. The first clafer after the comment was nested by its own column, which put the following lines at wrong levels.
* JSON output: the IR has the source positions of the clafers (`_cinPos`) and expressions (`_inPos`), which were always `null`: `{"file": "model.cfr", "start": {"line": 2, "column": 3}, "end": {"line": 2, "column": 6}}`, the file and the position in it, with lines and columns from 1 and an exclusive end. A tab advances the column to the next multiple of 8, plus 1, as in the compiler's error messages. The span of a clafer with children ends one or two columns after its last token, at the closing brace that the layout resolver inserts. Desugared expressions without a position in the model are still `null`.
* HTML output: comments are escaped and shown as written (`--add-comments`); markup in a comment was rendered, and `--` in a `//#` comment could end the generated HTML comment early.
* HTML output: each file of the model starts with its name (`<div class="file">model.cfr</div>`), also a model of one file, and the comments before a `//# FRAGMENT` directive are shown before it. The HTML shown for a model with errors gives their positions as `file.cfr:line:column`, and an error message with quotes no longer ends the tooltip.
* [Release](https://github.com/gsdlab/clafer/pull/101)

##### Clafer Version 0.5.3, Oct 15, 2026

Minor release: compiler fixes found with larger example models, the integer range of the Choco output, and a reorganized test suite.

* Type checker: no crash on arithmetic over `max`/`min` of a union, or on if/then/else over unions and dereferenced references.
* Alloy output: `a - b` was generated as `-a`; `parent` of a top-level abstract clafer is the union of the parent relations of its subclafers ([#84](https://github.com/gsdlab/clafer/issues/84)).
* References: `-> 1` lost the constant ([#89](https://github.com/gsdlab/clafer/issues/89)); redefinition of an inherited abstract clafer ([#86](https://github.com/gsdlab/clafer/issues/86)); Choco references to set expressions were dropped; unused abstract clafers named by a reference or a constraint are kept.
* Implicit `.dref` in unions (`BobPicks ++ 3`, `others ++ p1`); `sum` and `product` over a union.
* Inside a reference clafer, an ancestor (`Machine`, `parent`) is the enclosing instance, and the children of the target resolve through the reference.
* Scope inference covers the lower bound of group cardinalities.
* Sibling clafers on one line (`b : B A 3`) are a parse error.
* Alloy 6.2.0 (`alloy6.2.0.jar`, Java 17+) replaces Alloy 4.2; the generated Alloy models are unchanged. `--validate` runs all Alloy commands headlessly (`alloy exec`) and no longer opens the Alloy visualizer.
* New options `--minint` and `--maxint` (also in `//# OPTIONS`) set the integer range of the Choco output.
* The example models and regression tests run in the `model-tests` suite (flag `model-tests`, off by default) and are not part of the package.
* [Release](https://github.com/gsdlab/clafer/pull/99)

##### Clafer Version 0.5.2 released on Oct 9, 2026

Minor release, Haskell compatibility (GHC 9.6.7 and lts-22.44).

* [Release](https://github.com/gsdlab/clafer/pull/98)

##### Clafer Version 0.5.1 released on Sep 12, 2023

Minor release, latest Haskell compatibility (GHC 9.4.6 and LTS-21.11).

* [Release](https://github.com/gsdlab/clafer/pull/95)

##### Clafer Version 0.5.0 released on Jan 31, 2018

This major release adds behavioral modeling capability to Clafer.

* [Release](https://github.com/gsdlab/clafer/pull/94)

##### Clafer Version 0.4.5 released on Mar 13, 2017

* [Release](https://github.com/gsdlab/clafer/pull/91)

##### Clafer Version 0.4.4 released on Jun 23, 2016

* [Release](https://github.com/gsdlab/clafer/pull/88)

##### Clafer Version 0.4.3 released on Dec 22, 2015

* [Release](https://github.com/gsdlab/clafer/pull/81)

##### Clafer Version 0.4.2.1 released on Oct 19, 2015

* Fixed Haddock build, updated README, fixed a test case.

##### Clafer Version 0.4.2 released on Oct 16, 2015

* [Release](https://github.com/gsdlab/clafer/pull/74)

##### Clafer Version 0.4.1 released on Sep 1, 2015

* [Release](https://github.com/gsdlab/clafer/pull/71)

##### Clafer Version 0.4.0 released on Jul 28, 2015

* [Release](https://github.com/gsdlab/clafer/pull/68)

##### Clafer Version 0.3.10 released on April 24, 2015

* [Release](https://github.com/gsdlab/clafer/pull/66)

##### Clafer Version 0.3.9 released on March 06, 2015

* [Release](https://github.com/gsdlab/clafer/pull/63)

##### Clafer Version 0.3.8 released on January 27, 2015

* [Release](https://github.com/gsdlab/clafer/pull/60)

##### Clafer Version 0.3.7 released on October 23, 2014

* [Release](https://github.com/gsdlab/clafer/pull/53)

##### Clafer Version 0.3.6.1 released on July 08, 2014

* [Release](https://github.com/gsdlab/clafer/pull/50)

##### Clafer Version 0.3.6 released on May 23, 2014

* [Release](https://github.com/gsdlab/clafer/pull/48)

##### Clafer Version 0.3.5 released on January 20, 2014

* [Release](https://github.com/gsdlab/clafer/pull/44)

##### Clafer Version 0.3.4 released on September 20, 2013

##### Clafer Version 0.3.3 released on August 14, 2013

* [Release](https://github.com/gsdlab/clafer/pull/35)

##### Clafer Version 0.3.2 released on April 11, 2013

##### Clafer Version 0.3.1 released on October 17, 2012

##### Clafer Version 0.3 released on July 17, 2012

This was the first release of Clafer and included all code since the beginning of the project.

Basic features - See the `README.md`.
