../clafer --nr dataset/sqlite_scaled_tiny.cfr
../clafer --mode=xml --nr dataset/sqlite_scaled_tiny.cfr
python py_src/SPL_Configurator_clafer_generator.py --sparseintegers dataset/sqlite_scaled_tiny.xml >> dataset/sqlite_scaled_tiny.als 
java -jar /Users/rafaelolaechea/Downloads/alloy_moo.jar ~/clafer/spl_configurator/dataset/sqlite_scaled_tiny.als