./clafer -n spl_configurator/dataset/telematics_multi_objective_optimization.cfr
./clafer --mode=xml -n spl_configurator/dataset/telematics_multi_objective_optimization.cfr
python spl_configurator/py_src/SPL_Configurator_clafer_generator.py --property=cost --sparseintegers spl_configurator/dataset/telematics_multi_objective_optimization.xml >> spl_configurator/dataset/telematics_multi_objective_optimization.als 
java -jar /Users/rafaelolaechea/Downloads/alloy_moo.jar ~/clafer/spl_configurator/dataset/telematics_multi_objective_optimization.als