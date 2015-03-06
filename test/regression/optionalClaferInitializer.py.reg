from jsir.IR import *

c0_intVal = Clafer("c0_intVal").withCard(0, 1);
c0_stringVal = Clafer("c0_stringVal").withCard(0, 1);
c0_intVal.refTo("int");
c0_stringVal.refTo(string);
Constraint(implies(some(glob(c0_intVal)), equal(joinRef(glob(c0_intVal)), constant(1))));
Constraint(implies(some(glob(c0_stringVal)), equal(joinRef(glob(c0_stringVal)), constant("\"aaa\""))));
defaultScope(1);
stringLength(16);
