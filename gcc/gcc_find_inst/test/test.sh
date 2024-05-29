#!/bin/bash
touch /tmp/output.txt
COND_FILE="cond_all.txt" PROP_FILE="prop_all.txt" OUTPUT_FILE="/tmp/output.txt" ../gcc-bin/bin/gcc -fsanitize-coverage=trace-pc -O0 -g all.c -o prog
rm prog
cat /tmp/output.txt
rm /tmp/output.txt