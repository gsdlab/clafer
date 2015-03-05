from jsir.IR import *

c0_Person = Clafer("c0_Person").withCard(1, 1);
c0_maritalStatus = c0_Person.addChild("c0_maritalStatus").withCard(1, 1);
c0_married = c0_maritalStatus.addChild("c0_married").withCard(1, 1);
c0_married.addConstraint(some(joinParent(joinParent($this()))));
defaultScope(1);
stringLength(16);
