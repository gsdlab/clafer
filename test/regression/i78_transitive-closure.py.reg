from jsir.IR import *

c0_TimeLevel = Abstract("c0_TimeLevel");
c0_YearLevel = Abstract("c0_YearLevel").extending(c0_TimeLevel);
c0_MonthLevel = Abstract("c0_MonthLevel").extending(c0_TimeLevel);
c0_WeekLevel = Abstract("c0_WeekLevel").extending(c0_TimeLevel);
c0_aggregatesTo = c0_TimeLevel.addChild("c0_aggregatesTo").withCard(0, 1);
c0_Year2012 = Clafer("c0_Year2012").withCard(1, 1).extending(c0_YearLevel);
c0_Jan2012 = Clafer("c0_Jan2012").withCard(1, 1).extending(c0_MonthLevel);
c0_Week1 = Clafer("c0_Week1").withCard(1, 1).extending(c0_WeekLevel);
c0_Week1AggregatesTo = Clafer("c0_Week1AggregatesTo");
c0_aggregatesTo.refTo(c0_TimeLevel);
c0_Week1AggregatesTo.refToUnique(c0_TimeLevel);
Constraint(set_in(joinRef(join(glob(c0_Week1), c0_aggregatesTo)), joinRef(glob(c0_Week1AggregatesTo))));
Constraint(set_in(joinRef(join(joinRef(join(glob(c0_Week1), c0_aggregatesTo)), c0_aggregatesTo)), joinRef(glob(c0_Week1AggregatesTo))));
Constraint(equal(joinRef(glob(c0_Week1AggregatesTo)), set_union(glob(c0_Jan2012), glob(c0_Year2012))));
c0_YearLevel.addConstraint(none(join($this(), c0_aggregatesTo)));
c0_MonthLevel.addConstraint(set_in(joinRef(join($this(), c0_aggregatesTo)), glob(c0_YearLevel)));
c0_WeekLevel.addConstraint(set_in(joinRef(join($this(), c0_aggregatesTo)), glob(c0_MonthLevel)));
c0_Jan2012.addConstraint(equal(joinRef(join($this(), c0_aggregatesTo)), glob(c0_Year2012)));
c0_Week1.addConstraint(equal(joinRef(join($this(), c0_aggregatesTo)), glob(c0_Jan2012)));
scope({c0_TimeLevel:3, c0_Week1AggregatesTo:3, c0_aggregatesTo:3});
defaultScope(1);
stringLength(16);
