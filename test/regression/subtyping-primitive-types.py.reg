from jsir.IR import *

c0_percent = Abstract("c0_percent");
c0_date = Abstract("c0_date");
c0_time = Abstract("c0_time");
c0_twoPercent = Clafer("c0_twoPercent").withCard(1, 1).extending(c0_percent);
c0_threePercent = Clafer("c0_threePercent").withCard(1, 1).extending(c0_percent);
c0_today = Clafer("c0_today").withCard(1, 1).extending(c0_date);
c0_minute = c0_time.addChild("c0_minute").withCard(1, 1);
c0_hour = c0_time.addChild("c0_hour").withCard(1, 1);
c0_now = Clafer("c0_now").withCard(1, 1).extending(c0_time);
c0_percent.refTo("int");
c0_date.refTo(string);
c0_time.refTo("int");
c0_minute.refTo("int");
c0_hour.refTo("int");
Constraint(implies(some(glob(c0_twoPercent)), equal(joinRef(glob(c0_twoPercent)), constant(2))));
Constraint(implies(some(glob(c0_threePercent)), equal(joinRef(glob(c0_threePercent)), add(joinRef(glob(c0_twoPercent)), constant(1)))));
Constraint(implies(some(glob(c0_today)), equal(joinRef(glob(c0_today)), constant("\"Mar 20, 2012\""))));
Constraint(implies(some(glob(c0_time)), equal(joinRef(glob(c0_time)), add(joinRef(join(glob(c0_time), c0_minute)), joinRef(join(glob(c0_time), c0_hour))))));
c0_percent.addConstraint(and(greaterThanEqual(joinRef($this()), constant(0)), lessThanEqual(joinRef($this()), constant(5))));
c0_minute.addConstraint(and(greaterThanEqual(joinRef($this()), constant(0)), lessThanEqual(joinRef($this()), constant(5))));
c0_hour.addConstraint(and(greaterThanEqual(joinRef($this()), constant(0)), lessThanEqual(joinRef($this()), constant(5))));
c0_now.addConstraint(equal(joinRef(join($this(), c0_minute)), constant(3)));
c0_now.addConstraint(equal(joinRef(join($this(), c0_hour)), constant(1)));
scope({c0_percent:2});
defaultScope(1);
stringLength(16);
