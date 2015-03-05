from jsir.IR import *

c0_a = Clafer("c0_a").withCard(1, 1);
c0_b = Clafer("c0_b").withCard(1, 1);
c0_c = Clafer("c0_c").withCard(1, 1);
c0_a.refTo("int");
c0_b.refTo("int");
c0_c.refTo("int");
Constraint(implies(some(glob(c0_a)), equal(joinRef(glob(c0_a)), mod(constant(6), constant(4)))));
Constraint(equal(joinRef(glob(c0_a)), constant(2)));
Constraint(implies(some(glob(c0_b)), equal(joinRef(glob(c0_b)), mod(constant(0), constant(4)))));
Constraint(equal(joinRef(glob(c0_b)), constant(0)));
Constraint(implies(some(glob(c0_c)), equal(joinRef(glob(c0_c)), mod(constant(4), constant(2)))));
Constraint(equal(joinRef(glob(c0_c)), constant(0)));
defaultScope(1);
stringLength(16);
