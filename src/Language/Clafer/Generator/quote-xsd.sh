#!/bin/bash

# Author: Jimmy Liang
# Try: bash quote.sh myschemafile.xsd
# Result: creates a Haskell function named print_myschemafile that reproduces the file
filename=$(basename $1)
filename="${filename%%.*}"
#The name of the method is print_<filename>
echo "{-"
echo " Copyright (C) 2012 Jimmy Liang <http://gsd.uwaterloo.ca>"
echo ""
echo " Permission is hereby granted, free of charge, to any person obtaining a copy of"
echo " this software and associated documentation files (the \"Software\"), to deal in"
echo " the Software without restriction, including without limitation the rights to"
echo " use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies"
echo " of the Software, and to permit persons to whom the Software is furnished to do"
echo " so, subject to the following conditions:"
echo ""
echo " The above copyright notice and this permission notice shall be included in all"
echo " copies or substantial portions of the Software."
echo ""
echo " THE SOFTWARE IS PROVIDED \"AS IS\", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR"
echo " IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,"
echo " FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE"
echo " AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER"
echo " LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,"
echo " OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE"
echo " SOFTWARE."
echo "-}"
echo "module Language.Clafer.Generator.Schema where"
echo "xsd :: String"
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
