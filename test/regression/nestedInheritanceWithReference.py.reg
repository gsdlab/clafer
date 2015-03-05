from jsir.IR import *

c0_System = Abstract("c0_System");
c0_connections = c0_System.addChild("c0_connections");
c0_SystemX = Clafer("c0_SystemX").withCard(1, 1).extending(c0_System);
c0_con1 = c0_SystemX.addChild("c0_con1").withCard(1, 1).extending(c0_Connection);
c0_con2 = c0_SystemX.addChild("c0_con2").withCard(1, 1).extending(c0_Connection);
c0_SystemY = Clafer("c0_SystemY").withCard(1, 1).extending(c0_System);
c0_con3 = c0_SystemY.addChild("c0_con3").withCard(1, 1).extending(c0_Connection);
c0_con4 = c0_SystemY.addChild("c0_con4").withCard(1, 1).extending(c0_Connection);
c0_con5 = c0_SystemY.addChild("c0_con5").withCard(1, 1).extending(c0_Connection);
c0_connections.refToUnique(c0_Connection);
Constraint(equal(joinRef(join(glob(c0_SystemX), c0_connections)), set_union(join(glob(c0_SystemX), c0_con1), join(glob(c0_SystemX), c0_con2))));
Constraint(equal(joinRef(join(glob(c0_SystemY), c0_connections)), set_union(set_union(join(glob(c0_SystemY), c0_con3), join(glob(c0_SystemY), c0_con4)), join(glob(c0_SystemY), c0_con5))));
c0_System.addConstraint(equal(joinRef(join($this(), c0_connections)), join($this(), c0_Connection)));
scope({c0_Connection:5, c0_System:2, c0_connections:10});
defaultScope(1);
stringLength(16);
