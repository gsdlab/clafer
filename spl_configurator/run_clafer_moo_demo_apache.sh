../clafer --nr dataset/apache.cfr
../clafer --mode=xml --nr dataset/apache.cfr
python py_src/SPL_Configurator_clafer_generator.py --sparseintegers dataset/apache.xml >> dataset/apache.als 
java -jar /Users/rafaelolaechea/Downloads/alloy_moo.jar ~/clafer/spl_configurator/dataset/apache.als