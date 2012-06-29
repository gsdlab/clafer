../clafer --nr dataset/telematics_multi_objective_optimization.cfr
../clafer --mode=xml --nr dataset/telematics_multi_objective_optimization.cfr
python py_src/SPL_Configurator_clafer_generator.py --property=cost --sparseintegers dataset/telematics_multi_objective_optimization.xml >> dataset/telematics_multi_objective_optimization.als 
java -jar /Users/rafaelolaechea/Downloads/alloy_moo.jar ~/clafer/spl_configurator/dataset/telematics_multi_objective_optimization.als