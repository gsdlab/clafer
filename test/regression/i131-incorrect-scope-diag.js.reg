scope({c0_Animal:2, c0_Owner:2, c0_Pet:2, c0_leg:2});
defaultScope(1);
intRange(-8, 7);
stringLength(16);

c0_Animal = Abstract("c0_Animal");
c0_Owner = Abstract("c0_Owner");
c0_leg = c0_Animal.addChild("c0_leg");
c0_Pet = c0_Owner.addChild("c0_Pet").withCard(1, 1).extending(c0_Animal);
c0_SnakeOwner = Clafer("c0_SnakeOwner").withCard(1).extending(c0_Owner);
c0_DogOwner = Clafer("c0_DogOwner").withCard(1).extending(c0_Owner);
c0_SnakeOwner.addConstraint(none(join(join($this(), c0_Pet), c0_leg)));
c0_DogOwner.addConstraint(equal(card(join(join($this(), c0_Pet), c0_leg)), constant(4)));
