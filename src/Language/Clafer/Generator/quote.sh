#!/bin/bash

# Author: Jimmy Liang
# Try: bash quote.sh myschemafile.xsd
# Result: creates a Haskell function named print_myschemafile that reproduces the file

filename=$(basename $1)
filename="${filename%%.*}"
#The name of the method is print_<filename>
echo "module Language.Clafer.Generator.Schema where"
echo "xsd = concat [ \"\""

# Remove all Windows style carriage returns
#Set the internal field separator to empty string to preserve leading white space
tr -d '\r' < $1 | while IFS="" read line
do
        #Replace quotes with escaped quotes
        line=${line//\"/\\\"}
        echo "  , \"$line\n\"";
done

echo "  , \"\"]"
