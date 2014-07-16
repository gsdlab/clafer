defaultScope(1);
intRange(-8, 7);
stringLength(16);

c0_A = Clafer("c0_A").withCard(1, 1);
c0_b = c0_A.addChild("c0_b").withCard(0, 1);
c0_b.refTo(c0_A);
c0_A.addConstraint(some($this()));
c0_b.addConstraint(some(joinParent($this())));
