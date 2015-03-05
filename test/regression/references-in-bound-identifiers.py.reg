from jsir.IR import *

c0_A = Clafer("c0_A").withCard(1, 1);
c0_B = c0_A.addChild("c0_B");
c0_C = c0_B.addChild("c0_C").withCard(0, 1);
c0_B.refToUnique("int");
c0_A.addConstraint(all([decl([b = local("b")], join($this(), c0_B))], some(join(b, c0_C))));
c0_A.addConstraint(all([decl([b = local("b")], join($this(), c0_B))], equal(add(joinRef(b), constant(1)), constant(2))));
defaultScope(1);
stringLength(16);
