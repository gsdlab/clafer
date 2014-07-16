defaultScope(1);
intRange(-8, 7);
stringLength(16);

c0_intVal = Clafer("c0_intVal").withCard(0, 1);
c0_stringVal = Clafer("c0_stringVal").withCard(0, 1);
c0_intVal.refTo(Int);
c0_stringVal.refTo(string);
Constraint(implies(some(global(c0_intVal)), equal(joinRef(global(c0_intVal)), constant(1))));
Constraint(implies(some(global(c0_stringVal)), equal(joinRef(global(c0_stringVal)), constant("\"aaa\""))));
