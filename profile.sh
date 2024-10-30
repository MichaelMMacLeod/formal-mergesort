#!/usr/bin/env bash

FILES=$@

profile() {
    echo "Testing $1"
    for _ in {1..10}; do
        { time ./.lake/build/bin/lsort $@ --files $FILES > /dev/null ; } 2>&1 \
            | head -2 \
            | tail -1
    done
}

lake build lsort

profile --algorithm Array.mergeSortPartialFinUnsafe\\'
profile --algorithm Array.qsortOrd
profile --algorithm Array.mergeSortPartialFin
# profile --algorithm Array.mergeSortPartialUSizeUnsafe
# profile --algorithm Array.mergeSortPartialUSizeUnsafe\\'
# profile --algorithm qsort
