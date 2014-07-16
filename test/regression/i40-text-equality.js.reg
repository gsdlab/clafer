defaultScope(1);
intRange(-8, 7);
stringLength(16);

c0_text = Clafer("c0_text").withCard(1, 1);
c0_text1 = Clafer("c0_text1").withCard(1, 1);
c0_text2 = Clafer("c0_text2").withCard(1, 1);
c0_equal1 = Clafer("c0_equal1").withCard(0, 1);
c0_equal2 = Clafer("c0_equal2").withCard(0, 1);
c0_text.refTo(string);
c0_text1.refTo(string);
c0_text2.refTo(string);
Constraint(implies(some(global(c0_text)), equal(joinRef(global(c0_text)), constant("\"some text\""))));
Constraint(implies(some(global(c0_text1)), equal(joinRef(global(c0_text1)), constant("\"some text\""))));
Constraint(implies(some(global(c0_text2)), equal(joinRef(global(c0_text2)), constant("\"some text\""))));
Constraint(some(global(c0_equal1)));
Constraint(some(global(c0_equal2)));
c0_equal1.addConstraint(equal(joinRef(global(c0_text)), joinRef(global(c0_text1))));
c0_equal2.addConstraint(equal(joinRef(global(c0_text1)), joinRef(global(c0_text2))));
