from jsir.IR import *

c0_a = Clafer("c0_a");
c0_b = c0_a.addChild("c0_b");
c0_c = c0_b.addChild("c0_c");
c0_d = c0_c.addChild("c0_d").withCard(0, 1);
Constraint(all([decl([x = local("x")], join(join(glob(c0_a), c0_b), c0_c))], one(join(x, c0_d))));
Constraint(all([decl([x = local("x")], join(join(glob(c0_a), c0_b), c0_c))], some(join(x, c0_d))));
c0_a.addConstraint(all([decl([x = local("x")], join(join($this(), c0_b), c0_c))], one(join(x, c0_d))));
c0_b.addConstraint(one(join(join($this(), c0_c), c0_d)));
defaultScope(1);
stringLength(16);
