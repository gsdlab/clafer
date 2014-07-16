defaultScope(1);
intRange(-8, 7);
stringLength(16);

c0_claferA = Clafer("c0_claferA").withCard(1, 1);
c0_claferB = c0_claferA.addChild("c0_claferB").withCard(1, 1);
c0_claferC = c0_claferB.addChild("c0_claferC").withCard(1, 1);
c0_claferB.addConstraint(some(joinParent($this())));
c0_claferC.addConstraint(some(joinParent($this())));
c0_claferC.addConstraint(some(join(joinParent($this()), c0_claferC)));
