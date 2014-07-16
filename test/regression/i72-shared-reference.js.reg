scope({c0_Person:2, c0_WaitingLine:2, c0_participants:4});
defaultScope(1);
intRange(-8, 7);
stringLength(16);

c0_Person = Abstract("c0_Person");
c0_WaitingLine = Abstract("c0_WaitingLine");
c0_JohnDoe = Clafer("c0_JohnDoe").withCard(1, 1).extending(c0_Person);
c0_MaryJane = Clafer("c0_MaryJane").withCard(1, 1).extending(c0_Person);
c0_participants = c0_WaitingLine.addChild("c0_participants");
c0_BusLine = Clafer("c0_BusLine").withCard(1, 1).extending(c0_WaitingLine);
c0_JohnAndMaryLine = Clafer("c0_JohnAndMaryLine").withCard(1, 1).extending(c0_WaitingLine);
c0_participants.refToUnique(c0_Person);
c0_BusLine.addConstraint(and($in(global(c0_JohnDoe), joinRef(join($this(), c0_participants))), $in(global(c0_MaryJane), joinRef(join($this(), c0_participants)))));
c0_JohnAndMaryLine.addConstraint(equal(joinRef(join($this(), c0_participants)), union(global(c0_JohnDoe), global(c0_MaryJane))));
