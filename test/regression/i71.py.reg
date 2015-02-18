from jsir.IR import *

c0_Course = Abstract("c0_Course");
c0_Teacher = Abstract("c0_Teacher");
c0_taughtBy = c0_Course.addChild("c0_taughtBy");
c0_x = c0_taughtBy.addChild("c0_x").withCard(0, 1);
c0_teaches = c0_Teacher.addChild("c0_teaches");
c0_course = Clafer("c0_course").withCard(5, 5).extending(c0_Course);
c0_teacher = Clafer("c0_teacher").withCard(3, 3).extending(c0_Teacher);
c0_taughtBy.refToUnique(c0_Teacher);
c0_teaches.refToUnique(c0_Course);
Constraint(all([decl([c = local("c")], glob(c0_Course))], all([decl([t = local("t")], join(c, c0_taughtBy))], and(some(join(t, c0_x)), set_in(c, joinRef(join(joinRef(t), c0_teaches)))))));
scope({c0_Course:5, c0_Teacher:3, c0_course:5, c0_taughtBy:15, c0_teacher:3, c0_teaches:15, c0_x:15});
defaultScope(1);
stringLength(16);
