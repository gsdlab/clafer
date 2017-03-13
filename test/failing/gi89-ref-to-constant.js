scope({c0_ASIL:4});
defaultScope(1);
intRange(-8, 7);
stringLength(16);

c0_ASIL = Abstract("c0_ASIL");
c0_A = Clafer("c0_A").withCard(1, 1);
c0_B = Clafer("c0_B").withCard(1, 1);
c0_C = Clafer("c0_C").withCard(1, 1);
c0_D = Clafer("c0_D").withCard(1, 1);
c0_ASIL.refTo(Int);
c0_A.extending(c0_ASIL).refToUnique(Int);
c0_B.extending(c0_ASIL).refToUnique(Int);
c0_C.extending(c0_ASIL).refToUnique(Int);
c0_D.extending(c0_ASIL).refToUnique(Int);
assert(equal(joinRef(global(c0_A)), constant(1)));
assert(equal(joinRef(global(c0_B)), constant(2)));
assert(equal(joinRef(global(c0_C)), constant(3)));
assert(equal(joinRef(global(c0_D)), constant(4)));
