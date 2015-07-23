from jsir.IR import *

c0_Course = Abstract("c0_Course");
c0_TA = Abstract("c0_TA");
c0_assistants = c0_Course.addChild("c0_assistants");
c0_first = c0_TA.addChild("c0_first").withCard(0, 1);
c0_CompilerGradStudent = Clafer("c0_CompilerGradStudent").withCard(1, 1).extending(c0_TA);
c0_AIGradStudent = Clafer("c0_AIGradStudent").withCard(1, 1).extending(c0_TA);
c0_CompilerCourse = Clafer("c0_CompilerCourse").withCard(1, 1).extending(c0_Course);
c0_MachineLearningCourse = Clafer("c0_MachineLearningCourse").withCard(1, 1).extending(c0_Course);
c0_numerOfAssistants = Clafer("c0_numerOfAssistants").withCard(1, 1);
c0_assistants.refToUnique(c0_TA);
c0_first.refTo(c0_Course);
c0_numerOfAssistants.refTo("int");
Constraint(equal(joinRef(join(glob(c0_CompilerGradStudent), c0_first)), glob(c0_CompilerCourse)));
Constraint(equal(joinRef(join(glob(c0_AIGradStudent), c0_first)), glob(c0_MachineLearningCourse)));
Constraint(implies(some(glob(c0_numerOfAssistants)), equal(joinRef(glob(c0_numerOfAssistants)), card(join(glob(c0_Course), c0_assistants)))));
c0_first.addConstraint(set_in(joinParent($this()), joinRef(join(joinRef($this()), c0_assistants))));
scope({c0_Course:2, c0_TA:2, c0_assistants:4, c0_first:2});
defaultScope(1);
stringLength(16);
