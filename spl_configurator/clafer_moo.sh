#!/bin/bash
if [ $# -eq 2 ]
then
	cfrfile=$1
	pathtoclafertools=$2
else
    echo Usage: clafer_moo [MODEL] [PATH TO CLAFER TOOLS]
	exit 1
fi

directory=$(dirname "$cfrfile")
filename=$(basename "$cfrfile")
filename="${filename%.*}"

clafer --nr $cfrfile
clafer --mode=xml --nr $cfrfile
python $pathtoclafertools/py_src/SPL_Configurator_clafer_generator.py --sparseintegers ${directory:-"."}/${filename}.xml >> ${directory:-"."}/${filename}.als 
java -jar $pathtoclafertools/tools/alloy4moo.jar ${directory:-"."}/${filename}.als