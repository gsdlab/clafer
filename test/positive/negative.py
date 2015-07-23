from jsir.IR import *

c0_z = Clafer("c0_z").withCard(1, 1);
c0_y = c0_z.addChild("c0_y").withCard(1, 1);
c0_y.refTo("int");
c0_z.addConstraint(equal(joinRef(join($this(), c0_y)), constant(-1)));
defaultScope(1);
stringLength(16);
