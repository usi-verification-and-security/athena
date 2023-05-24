#!/bin/bash

smtChecker="$1" # tswc, lfsc, carcara, smtinterpol-checker
smtSolver="$2"  # opensmt, z3, verit, cvc5, cvc5-lfsc, cvc5-alethe, smtinterpol
target="$3"     # test, LIA-lin, LIA-nonlin
chcSolver="$4"  # golem, eldarica, spacer

if [[ "$#" -ne 4 ]]; then
  echo "Usage: $0 smtChecker smtSolver target chcSolver"
  exit 1
fi

if [[ "$smtChecker" != "tswc" && "$smtChecker" != "lfsc" && "$smtChecker" != "carcara" && "$smtChecker" != "smtinterpol-checker" ]]; then
    echo "smtChecker invalid: use tswc, lfsc, carcara, or smtinterpol-checker"
    exit 1
fi

if [[ "$smtSolver" != "opensmt" && "$smtSolver" != "z3" && "$smtSolver" != "verit" && "$smtSolver" != "cvc5" && "$smtSolver" != "cvc5-lfsc" && "$smtSolver" != "cvc5-alethe" && "$smtSolver" != "smtinterpol" ]]; then
    echo "smtSolver invalid: use opensmt, z3, verit, cvc5, cvc5-lfsc, cvc5-alethe, or smtinterpol"
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
cd ../results/result_${smtChecker}_${target}_${smtSolver}_$chcSolver

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
count_verified=0
count_holey=0
count_invalid=0
count_unknown=0
count_problem=0
count_uncategorized=0

count_entries "_timeout_smt_checker.stats"       "count_timeout"
count_entries "_memout_smt_checker.stats"        "count_memout"
count_entries "_verified_smt_checker.stats"      "count_verified"
count_entries "_holey_smt_checker.stats"         "count_holey"
count_entries "_invalid_smt_checker.stats"       "count_invalid"
count_entries "_unknown_smt_checker.stats"       "count_unknown"
count_entries "_problem_smt_checker.stats"       "count_problem"
count_entries "_uncategorized_smt_checker.stats" "count_uncategorized"

#########################

echo "********** Results for $smtChecker with $target from $smtSolver and $chcSolver **********"

total=$((count_verified + count_invalid + count_unknown + count_problem + count_timeout + count_memout + count_uncategorized))
echo "Benchmarks analysed: $total"

echo "verified: $count_verified ($count_holey verified but holey)"
echo "invalid: $count_invalid"
echo "unknown: $count_unknown"
echo "problem: $count_problem"
echo "timeout: $count_timeout"
echo "memout: $count_memout"
echo "uncategorized: $count_uncategorized"