from jsir.IR import *

c0_XX = Clafer("c0_XX").withCard(1, 1);
c0_x = c0_XX.addChild("c0_x").withCard(1, 1);
c0_y = c0_x.addChild("c0_y").withCard(1, 1);
c0_ZZ = Clafer("c0_ZZ").withCard(1, 1);
c0_z = c0_ZZ.addChild("c0_z").withCard(1, 1);
c1_y = c0_z.addChild("c1_y").withCard(1, 1);
c0_z.refTo("int");
c0_XX.addConstraint(some(join($this(), c0_x)));
c0_ZZ.addConstraint(greaterThan(joinRef(join($this(), c0_z)), constant(0)));
defaultScope(1);
stringLength(16);
