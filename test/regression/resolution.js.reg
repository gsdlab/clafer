defaultScope(1);
intRange(-8, 7);
stringLength(16);

c0_X = Clafer("c0_X").withCard(1, 1);
c0_x = c0_X.addChild("c0_x").withCard(1, 1);
c0_y = c0_x.addChild("c0_y").withCard(1, 1);
c0_Z = Clafer("c0_Z").withCard(1, 1);
c0_z = c0_Z.addChild("c0_z").withCard(1, 1);
c1_y = c0_z.addChild("c1_y").withCard(1, 1);
c0_z.refTo(Int);
c0_X.addConstraint(some(join($this(), c0_x)));
c0_Z.addConstraint(greaterThan(joinRef(join($this(), c0_z)), constant(0)));
