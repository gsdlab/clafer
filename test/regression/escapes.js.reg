scope({c0_Person:4, c0_spouse:4});
defaultScope(1);
intRange(-8, 7);
stringLength(16);

c0_Person = Abstract("c0_Person");
c0_spouse = c0_Person.addChild("c0_spouse").withCard(0, 1);
c0_Alice = Clafer("c0_Alice").withCard(1, 1).extending(c0_Person);
c0_Bob = Clafer("c0_Bob").withCard(1, 1).extending(c0_Person);
c0_Carol = Clafer("c0_Carol").withCard(1, 1).extending(c0_Person);
c0_Dave = Clafer("c0_Dave").withCard(1, 1).extending(c0_Person);
c0_spouse.refTo(c0_Person);
assert(equal(joinRef(join(global(c0_Bob), c0_spouse)), global(c0_Alice)));
assert(none(join(global(c0_Dave), c0_spouse)));
c0_Alice.addConstraint(equal(joinRef(join($this(), c0_spouse)), global(c0_Bob)));
c0_Carol.addConstraint(none(join($this(), c0_spouse)));

//symmetric[r_c0_spouse . c0_spouse_ref]
//irreflexive[r_c0_spouse . c0_spouse_ref]
