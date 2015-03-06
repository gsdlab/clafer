from jsir.IR import *

c0_Component = Abstract("c0_Component");
c0_TemperatureConnector = Abstract("c0_TemperatureConnector");
c0_input = c0_Port.addChild("c0_input").withCard(0, 1);
c0_output = c0_Port.addChild("c0_output").withCard(0, 1);
c0_from = c0_TemperatureConnector.addChild("c0_from").withCard(1, 1);
c0_to = c0_TemperatureConnector.addChild("c0_to").withCard(1, 1);
c0_sensor = Clafer("c0_sensor").withCard(1, 1).extending(c0_Component);
c0_temperature = c0_sensor.addChild("c0_temperature").withCard(1, 1).withGroupCard(1).extending(c0_TemperaturePort);
c0_controller = Clafer("c0_controller").withCard(1, 1).extending(c0_Component);
c1_temperature = c0_controller.addChild("c1_temperature").withCard(1, 1).withGroupCard(1).extending(c0_TemperaturePort);
c0_con1 = Clafer("c0_con1").withCard(1, 1).extending(c0_TemperatureConnector);
c0_TemperaturePort.refToUnique("int");
c0_from.refTo(c0_TemperaturePort);
c0_to.refTo(c0_TemperaturePort);
Constraint(equal(joinRef(join(glob(c0_controller), c1_temperature)), joinRef(join(glob(c0_sensor), c0_temperature))));
c0_TemperatureConnector.addConstraint(equal(joinRef(joinRef(join($this(), c0_to))), joinRef(joinRef(join($this(), c0_from)))));
c0_from.addConstraint(some(join(joinRef($this()), c0_output)));
c0_to.addConstraint(some(join(joinRef($this()), c0_input)));
c0_temperature.addConstraint(some(join($this(), c0_output)));
c1_temperature.addConstraint(some(join($this(), c0_input)));
c0_con1.addConstraint(equal(joinRef(join($this(), c0_from)), join(glob(c0_sensor), c0_temperature)));
c0_con1.addConstraint(equal(joinRef(join($this(), c0_to)), join(glob(c0_controller), c1_temperature)));
scope({c0_Component:2, c0_Port:2, c0_TemperaturePort:2, c0_input:2, c0_output:2});
defaultScope(1);
stringLength(16);
