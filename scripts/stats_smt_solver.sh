#!/bin/bash

smtSolver="$1" # opensmt, z3, verit, cvc5, cvc5-lfsc, cvc5-alethe, smtinterpol
smtMode="$2"   # proof, noProof
target="$3"    # test, LIA-lin, LIA-nonlin
chcSolver="$4" # golem, eldarica, spacer

if [[ "$#" -ne 4 ]]; then
  echo "Usage: $0 smtSolver smtMode target chcSolver"
  exit 1
fi

if [[ "$smtSolver" != "opensmt" && "$smtSolver" != "z3" && "$smtSolver" != "verit" && "$smtSolver" != "cvc5" && "$smtSolver" != "cvc5-lfsc" && "$smtSolver" != "cvc5-alethe" && "$smtSolver" != "smtinterpol" ]]; then
    echo "smtSolver invalid: use opensmt, z3, verit, cvc5, cvc5-lfsc, cvc5-alethe, or smtinterpol"
    exit 1
fi

if [[ "$smtMode" != "proof" && "$smtMode" != "noProof" ]]; then
    echo "smtMode invalid: use proof, or noProof"
    exit 1
fi

if [[ "$target" != "test" && "$target" != "LIA-lin" && "$target" != "LIA-nonlin" ]]; then
    echo "target invalid: use test, LIA-lin, or LIA-nonlin"
    exit 1
fi

if [[ "$chcSolver" != "golem" && "$chcSolver" != "eldarica" && "$chcSolver" != "spacer" ]]; then
    echo "chcSolver invalid: use golem, eldarica, or spacer"
    exit 1
fi

#########################

cd "$(dirname "$0")" # script's folder
cd ../results/result_${smtSolver}_${smtMode}_${target}_$chcSolver

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
count_unsupported=0
count_problem=0
count_uncategorized=0

count_entries "_timeout_smt_solver.stats"       "count_timeout"
count_entries "_memout_smt_solver.stats"        "count_memout"
count_entries "_sat_smt_solver.stats"           "count_sat"
count_entries "_unsat_smt_solver.stats"         "count_unsat"
count_entries "_unknown_smt_solver.stats"       "count_unknown"
count_entries "_unsupported_smt_solver.stats"   "count_unsupported"
count_entries "_problem_smt_solver.stats"       "count_problem"
count_entries "_uncategorized_smt_solver.stats" "count_uncategorized"

#########################

echo "********** Results for $smtSolver in $smtMode mode with $target from $chcSolver **********"

total=$((count_sat + count_unsat + count_unknown + count_unsupported + count_problem + count_timeout + count_memout + count_uncategorized))
echo "Benchmarks analysed: $total"

echo "sat: $count_sat"
echo "unsat: $count_unsat"
echo "unknown: $count_unknown"
echo "unsupported: $count_unsupported"
echo "problem: $count_problem"
echo "timeout: $count_timeout"
echo "memout: $count_memout"
echo "uncategorized: $count_uncategorized"