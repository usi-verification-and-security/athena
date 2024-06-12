#!/bin/bash

smtChecker="$1"    # alfc, carcara, lfsc, smtinterpol-checker, tswc
smtSolver="$2"     # cvc5-lfsc, cvc5-alethe, cvc5-aletheLF, opensmt, smtinterpol, verit, z3
target="$3"        # test, LIA-lin, LIA-nonlin, LIA-Arrays-lin, LIA-Arrays-nonlin
chcSolver="$4"     # eldarica, golem, spacer
printForLatex="$5" # true, false

if [[ "$#" -ne 5 ]]; then
  echo "Usage: $0 smtChecker smtSolver target chcSolver printForLatex"
  exit 1
fi

if [[ "$smtChecker" != "alfc" && "$smtChecker" != "carcara" && "$smtChecker" != "lfsc" && "$smtChecker" != "smtinterpol-checker" && "$smtChecker" != "tswc" ]]; then
    echo "smtChecker invalid: use alfc, carcara, lfsc, smtinterpol-checker, or tswc"
    exit 1
fi

if [[ "$smtSolver" != "cvc5-lfsc" && "$smtSolver" != "cvc5-alethe" && "$smtSolver" != "cvc5-aletheLF" && "$smtSolver" != "opensmt" && "$smtSolver" != "smtinterpol" && "$smtSolver" != "verit" && "$smtSolver" != "z3" ]]; then
    echo "smtSolver invalid: use cvc5-lfsc, cvc5-alethe, cvc5-aletheLF, opensmt, smtinterpol, verit, or z3"
    exit 1
fi

if [[ "$target" != "test" && "$target" != "LIA-lin" && "$target" != "LIA-nonlin" && "$target" != "LIA-Arrays-lin" && "$target" != "LIA-Arrays-nonlin" ]]; then
    echo "target invalid: use test, LIA-lin, LIA-nonlin, LIA-Arrays-lin, or LIA-Arrays-nonlin"
    exit 1
fi

if [[ "$chcSolver" != "eldarica" && "$chcSolver" != "golem" && "$chcSolver" != "spacer" ]]; then
    echo "chcSolver invalid: use eldarica, golem, or spacer"
    exit 1
fi

if [[ "$printForLatex" != "true" && "$printForLatex" != "false" ]]; then
    printForLatex=false
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

count_verified=$((count_verified + count_holey))

if [[ "$printForLatex" == "false" ]]; then
    total=$((count_verified + count_invalid + count_unknown + count_problem + count_timeout + count_memout + count_uncategorized))

    echo "********** Results for $smtChecker with $target from $smtSolver and $chcSolver **********"    
    echo "Benchmarks analysed: $total"
    echo "verified: $count_verified ($count_holey verified but holey)"
    echo "invalid: $count_invalid"
    echo "unknown: $count_unknown"
    echo "timeout: $count_timeout"
    echo "memout: $count_memout"
    echo "problem: $count_problem"
    echo "uncategorized: $count_uncategorized"
else
    if [[ "$smtChecker" == "alfc" ]]; then
        smtCheckerLatex="\alfc{}"
    elif [[ "$smtChecker" == "carcara" ]]; then
        smtCheckerLatex="\carcara{}"
    elif [[ "$smtChecker" == "lfsc" ]]; then
        smtCheckerLatex="\lfsc{}"
    elif [[ "$smtChecker" == "smtinterpol-checker" ]]; then
        smtCheckerLatex="\smtinterpol{}"
    elif [[ "$smtChecker" == "tswc" ]]; then
        smtCheckerLatex="\tswc{}"
    fi

    echo "        & $smtCheckerLatex"
    echo "            & $count_verified"
    echo "            & $count_invalid"
    echo "            & $count_timeout"
    echo "            & $count_memout"
    echo "            & $count_problem \\\\"
fi
