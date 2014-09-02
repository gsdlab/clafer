#!/bin/bash

for file in ${1:-*.cfr}; do
	echo "=========================="
  echo "==== $file "
  echo "=========================="
  cat $file
  clafer -m=clafer -o "$file"
done

