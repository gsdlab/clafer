from jsir.IR import *

c0_rate = Clafer("c0_rate").withCard(1, 1);
c0_interest = Clafer("c0_interest").withCard(1, 1);
c0_rate.refTo(real);
c0_interest.refTo(real);
Constraint(equal(joinRef(glob(c0_rate)), constant(1.99)));
Constraint(implies(some(glob(c0_interest)), equal(joinRef(glob(c0_interest)), mul(constant(100), joinRef(glob(c0_rate))))));
defaultScope(1);
stringLength(16);
