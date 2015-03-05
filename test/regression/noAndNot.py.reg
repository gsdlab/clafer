from jsir.IR import *

c0_Person = Abstract("c0_Person");
c0_married = c0_Person.addChild("c0_married").withCard(0, 1);
c0_child = c0_Person.addChild("c0_child");
c0_Alice = Clafer("c0_Alice").withCard(1, 1).extending(c0_Person);
c0_child.refToUnique(c0_Person);
c0_Alice.addConstraint(none(join($this(), c0_married)));
c0_Alice.addConstraint(none(join($this(), c0_child)));
defaultScope(1);
stringLength(16);
