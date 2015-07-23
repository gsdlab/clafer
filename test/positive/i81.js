scope({c0_a:0});
defaultScope(1);
intRange(-8, 7);
stringLength(16);

c0_a = Abstract("c0_a");
c0_b = Clafer("c0_b").withCard(1, 1);
c0_c = Clafer("c0_c").withCard(0, 1);
Constraint(some(global(c0_a)));
