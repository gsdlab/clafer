#!/bin/bash
if [ $# -gt 0 ]
    then
    
     fullfile=$1
else
    fullfile="dataset/telematics_multi_objective_optimization.cfr"
fi

directory=$(dirname "$fullfile")
filename=$(basename "$fullfile")
extension="${filename##*.}"
filename="${filename%.*}"

../clafer --nr $fullfile
../clafer --mode=xml --nr $fullfile
python py_src/SPL_Configurator_clafer_generator.py --sparseintegers ${directory:-"."}/${filename}.xml >> ${directory:-"."}/${filename}.als 
java -jar ../tools/alloy_moo.jar ${directory:-"."}/${filename}.als