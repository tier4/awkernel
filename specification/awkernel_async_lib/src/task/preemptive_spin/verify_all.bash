#!/bin/bash

LTLS=(ensure_priority eventually_prerequisites eventually_terminate)
SCHED_TYPE_PATTERNS=(0 1 2 3)

for sched_type_pattern in ${SCHED_TYPE_PATTERNS[@]}; do
    for ltl in ${LTLS[@]}; do
        echo "==============================================================="
        echo "Verifying with LTL=$ltl and sched_type_pattern=$sched_type_pattern"
        echo "==============================================================="

        rm -f pan.* *.trail pan *.tmp
        spin -DSCHED_TYPE_PATTERN=$sched_type_pattern -a preemptive.pml
        gcc -O3 -DCOLLAPSE -DVECTORSZ=5000 -DNFAIR=3 -o pan pan.c
        ./pan -a -n -m30000 -N $ltl

        echo ""
    done
done
