defaultScope(1);
intRange(-8, 7);
stringLength(16);

c0_AliceAge = Clafer("c0_AliceAge").withCard(1, 1);
c0_BobAge = Clafer("c0_BobAge").withCard(1, 1);
c0_BobsBirthday = Clafer("c0_BobsBirthday").withCard(0, 1);
c0_AliceAge.refTo(Int);
c0_BobAge.refTo(Int);
Constraint(equal(ifThenElse(some(global(c0_BobsBirthday)), joinRef(global(c0_BobAge)), joinRef(global(c0_AliceAge))), constant(5)));
