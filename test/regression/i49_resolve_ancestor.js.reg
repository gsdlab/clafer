defaultScope(1);
intRange(-8, 7);
stringLength(16);

c0_person = Clafer("c0_person").withCard(1, 1);
c0_haha = c0_person.addChild("c0_haha").withCard(1, 1);
c0_lala = c0_haha.addChild("c0_lala").withCard(1, 1);
c0_age = c0_lala.addChild("c0_age").withCard(1, 1);
c0_ble = c0_person.addChild("c0_ble").withCard(1, 1);
c0_married = c0_ble.addChild("c0_married").withCard(0, 1);
c0_age.refTo(Int);
c0_married.addConstraint(greaterThanEqual(joinRef(join(join(join(joinParent(joinParent($this())), c0_haha), c0_lala), c0_age)), constant(18)));
