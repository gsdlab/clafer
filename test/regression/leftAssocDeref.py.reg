from jsir.IR import *

c0_x = Clafer("c0_x").withCard(1, 1);
c0_y = Clafer("c0_y").withCard(1, 1);
c0_z = Clafer("c0_z").withCard(1, 1);
c0_x.refTo("int");
c0_y.refTo(c0_x);
c0_z.refTo(c0_y);
Constraint(equal(joinRef(glob(c0_x)), constant(1)));
Constraint(equal(joinRef(glob(c0_x)), constant(1)));
Constraint(equal(joinRef(joinRef(glob(c0_y))), constant(1)));
Constraint(equal(joinRef(joinRef(glob(c0_y))), constant(1)));
Constraint(equal(joinRef(joinRef(glob(c0_y))), constant(1)));
Constraint(equal(joinRef(joinRef(joinRef(glob(c0_z)))), constant(1)));
Constraint(equal(joinRef(joinRef(joinRef(glob(c0_z)))), constant(1)));
Constraint(equal(joinRef(joinRef(joinRef(glob(c0_z)))), constant(1)));
Constraint(equal(joinRef(joinRef(joinRef(glob(c0_z)))), constant(1)));
c0_x.addConstraint(equal(joinRef($this()), constant(1)));
c0_x.addConstraint(equal(joinRef($this()), constant(1)));
c0_y.addConstraint(equal(joinRef(joinRef($this())), constant(1)));
c0_y.addConstraint(equal(joinRef(joinRef($this())), constant(1)));
c0_y.addConstraint(equal(joinRef(joinRef($this())), constant(1)));
c0_z.addConstraint(equal(joinRef(joinRef(joinRef($this()))), constant(1)));
c0_z.addConstraint(equal(joinRef(joinRef(joinRef($this()))), constant(1)));
c0_z.addConstraint(equal(joinRef(joinRef(joinRef($this()))), constant(1)));
c0_z.addConstraint(equal(joinRef(joinRef(joinRef($this()))), constant(1)));
defaultScope(1);
stringLength(16);
