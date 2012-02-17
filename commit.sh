#!/bin/sh
make newVersion
git commit -a -m "$1"
git push