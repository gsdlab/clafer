from jsir.IR import *

c0_A = Clafer("c0_A").withCard(1, 1);
c0_x = c0_A.addChild("c0_x").withCard(0, 1);
c0_y = c0_A.addChild("c0_y").withCard(0, 1);
c0_A.addConstraint(and(implies(some(join($this(), c0_x)), none(join($this(), c0_y))), implies(some(join($this(), c0_y)), none(join($this(), c0_x)))));
defaultScope(1);
stringLength(16);
