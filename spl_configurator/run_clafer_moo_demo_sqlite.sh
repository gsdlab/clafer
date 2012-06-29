./clafer -n spl_configurator/dataset/sqlite_scaled_tiny.cfr
./clafer --mode=xml -n spl_configurator/dataset/sqlite_scaled_tiny.cfr
python spl_configurator/py_src/SPL_Configurator_clafer_generator.py --property=footprint --sparseintegers spl_configurator/dataset/sqlite_scaled_tiny.xml >> spl_configurator/dataset/sqlite_scaled_tiny.als 
java -jar /Users/rafaelolaechea/Downloads/alloy_moo.jar ~/clafer/spl_configurator/dataset/sqlite_scaled_tiny.als