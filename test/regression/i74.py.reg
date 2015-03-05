from jsir.IR import *

c0_Kernel = Abstract("c0_Kernel");
c0_memory = c0_Kernel.addChild("c0_memory").withCard(0, 1);
c0_Phone = Clafer("c0_Phone").withCard(1, 1);
c0_name = c0_Phone.addChild("c0_name").withCard(1, 1);
c0_name.refTo(string);
c0_Phone.addConstraint(some(join(glob(c0_Kernel), c0_memory)));
scope({c0_Kernel:0, c0_memory:0});
defaultScope(1);
stringLength(16);
