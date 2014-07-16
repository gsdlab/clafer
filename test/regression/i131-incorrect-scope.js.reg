scope({c0_Animal:2, c0_leg:2});
defaultScope(1);
intRange(-8, 7);
stringLength(16);

c0_Animal = Abstract("c0_Animal");
c0_leg = c0_Animal.addChild("c0_leg");
c0_Dog = Clafer("c0_Dog").extending(c0_Animal);
c0_Spider = Clafer("c0_Spider").extending(c0_Animal);
c0_Dog.addConstraint(equal(card(join($this(), c0_leg)), constant(4)));
c0_Spider.addConstraint(equal(card(join($this(), c0_leg)), constant(8)));
