#!/bin/bash
rm -rf codeql_database _codeql_detected_source_root
make clean
echo "src/main.c" > /tmp/filter.txt
FILTER_FILE=/tmp/filter.txt codeql database create -l cpp --overwrite --extra-tracing-config=../custom-tracing-config.lua codeql_database