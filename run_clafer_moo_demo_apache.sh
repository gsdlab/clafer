./clafer -n spl_configurator/dataset/apache.cfr
./clafer --mode=xml -n spl_configurator/dataset/apache.cfr
python spl_configurator/py_src/SPL_Configurator_clafer_generator.py --property=performance --sparseintegers spl_configurator/dataset/apache.xml >> spl_configurator/dataset/apache.als 
java -jar /Users/rafaelolaechea/Downloads/alloy_moo.jar ~/clafer/spl_configurator/dataset/apache.als