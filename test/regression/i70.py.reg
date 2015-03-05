from jsir.IR import *

c0_Clafer1 = Clafer("c0_Clafer1").withCard(1, 1);
c0_type = c0_Clafer1.addChild("c0_type").withCard(1, 1).withGroupCard(1, 1);
c0_Type1 = c0_type.addChild("c0_Type1").withCard(0, 1);
c0_Type2 = c0_type.addChild("c0_Type2").withCard(0, 1);
c0_Clafer2 = Clafer("c0_Clafer2").withCard(1, 1);
c0_clafer1 = c0_Clafer2.addChild("c0_clafer1").withCard(1, 1);
c1_type = c0_Clafer2.addChild("c1_type").withCard(1, 1).withGroupCard(1, 1);
c1_Type1 = c1_type.addChild("c1_Type1").withCard(0, 1);
c1_Type2 = c1_type.addChild("c1_Type2").withCard(0, 1);
c0_clafer1.refTo(c0_Clafer1);
c0_Clafer2.addConstraint(implies(some(join(join($this(), c1_type), c1_Type1)), some(join(join(joinRef(join($this(), c0_clafer1)), c0_type), c0_Type2))));
c0_Clafer2.addConstraint(implies(some(join(join($this(), c1_type), c1_Type1)), some(join(join(joinRef(join($this(), c0_clafer1)), c0_type), c0_Type2))));
defaultScope(1);
stringLength(16);
