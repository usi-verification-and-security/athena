#!/bin/bash

chcSolver="$1" # golem, eldarica, spacer
target="$2"    # test, LIA-lin, LIA-nonlin

if [[ "$#" -ne 2 ]]; then
  echo "Usage: $0 chcSolver target"
  exit 1
fi

if [[ "$chcSolver" != "golem" && "$chcSolver" != "eldarica" && "$chcSolver" != "spacer" ]]; then
    echo "solver invalid: use golem, eldarica, or spacer"
    exit 1
fi

if [[ "$target" != "test" && "$target" != "LIA-lin" && "$target" != "LIA-nonlin" ]]; then
    echo "target invalid: use test, LIA-lin, or LIA-nonlin"
    exit 1
fi

#########################

cd "$(dirname "$0")" # script's folder
cd ../results/witnesses_${chcSolver}_$target

#########################

function count_entries () {
    # $1 file name
    # $2 counter variable name

    if test -f "$1"; then
        if [[ $(wc -w < "$1") -gt 0 ]]; then
            while IFS= read -r line; do
                eval "$2=$(($2+1))"
            done < "$1"
        fi
    fi
}

#########################

count_timeout=0
count_memout=0
count_sat=0
count_unsat=0
count_unknown=0
count_problem=0
count_uncategorized=0
count_quantifiers=0

count_entries "_timeout_chc_solver.stats"       "count_timeout"
count_entries "_memout_chc_solver.stats"        "count_memout"
count_entries "_sat_chc_solver.stats"           "count_sat"
count_entries "_unsat_chc_solver.stats"         "count_unsat"
count_entries "_unknown_chc_solver.stats"       "count_unknown"
count_entries "_problem_chc_solver.stats"       "count_problem"
count_entries "_uncategorized_chc_solver.stats" "count_uncategorized"
count_entries "_quantifiers_chc_solver.stats"   "count_quantifiers"

#########################

echo "********** Results for $1 with $2 **********"

total=$((count_sat + count_unsat + count_unknown + count_problem + count_timeout + count_memout + count_uncategorized))
echo "Benchmarks analysed: $total"

echo "sat: $count_sat ($count_quantifiers sat witnesses with quantifiers)"
echo "unsat: $count_unsat"
echo "unknown: $count_unknown"
echo "problem: $count_problem"
echo "timeout: $count_timeout"
echo "memout: $count_memout"
echo "uncategorized: $count_uncategorized"