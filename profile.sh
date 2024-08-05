#!/usr/bin/env bash

profile() {
    echo "Testing $1"
    for _ in {1..10}; do
        { time ./.lake/build/bin/lsort --"$1" < ./test-input/10-million-lines.txt > /dev/null ; } 2>&1 \
            | head -2 \
            | tail -1
    done
}

lake build lsort

# profile mergeSortPartial
profile mergeSort
# profile mergeSortUnsafe
profile qsort
# profile heapSort
