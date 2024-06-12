#!/bin/bash

smtSolver="$1"     # cvc5, cvc5-lfsc, cvc5-alethe, cvc5-aletheLF, opensmt, smtinterpol, verit, z3
smtMode="$2"       # proof, noProof
target="$3"        # test, LIA-lin, LIA-nonlin, LIA-Arrays-lin, LIA-Arrays-nonlin
chcSolver="$4"     # eldarica, golem, spacer
printForLatex="$5" # true, false

if [[ "$#" -ne 5 ]]; then
  echo "Usage: $0 smtSolver smtMode target chcSolver printForLatex"
  exit 1
fi

if [[ "$smtSolver" != "cvc5" && "$smtSolver" != "cvc5-lfsc" && "$smtSolver" != "cvc5-alethe" && "$smtSolver" != "cvc5-aletheLF" && "$smtSolver" != "opensmt" && "$smtSolver" != "smtinterpol" && "$smtSolver" != "verit" && "$smtSolver" != "z3" ]]; then
    echo "smtSolver invalid: use cvc5, cvc5-lfsc, cvc5-alethe, cvc5-aletheLF, opensmt, smtinterpol, verit, z3"
    exit 1
fi

if [[ "$smtMode" != "proof" && "$smtMode" != "noProof" ]]; then
    echo "smtMode invalid: use proof, or noProof"
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

if [[ "$printForLatex" == "false" ]]; then
    total=$((count_sat + count_unsat + count_unknown + count_unsupported + count_problem + count_timeout + count_memout + count_uncategorized))

    echo "********** Results for $smtSolver in $smtMode mode with $target from $chcSolver **********"
    echo "Benchmarks analysed: $total"
    echo "sat: $count_sat"
    echo "unsat: $count_unsat"
    echo "unknown: $count_unknown"
    echo "timeout: $count_timeout"
    echo "memout: $count_memout"
    echo "problem: $count_problem"
    echo "unsupported: $count_unsupported"
    echo "uncategorized: $count_uncategorized"
else
    if [[ "$smtSolver" == "cvc5" ]]; then
        smtSolverLatex="\cvc{}"
    elif [[ "$smtSolver" == "cvc5-lfsc" ]]; then
        smtSolverLatex="\cvc-\lfsc{}"
    elif [[ "$smtSolver" == "cvc5-alethe" ]]; then
        smtSolverLatex="\cvc-\alethe{}"
    elif [[ "$smtSolver" == "cvc5-aletheLF" ]]; then
        smtSolverLatex="\cvc-\alethelf{}"
    elif [[ "$smtSolver" == "opensmt" ]]; then
        smtSolverLatex="\osmt{}"
    elif [[ "$smtSolver" == "smtinterpol" ]]; then
        smtSolverLatex="\smtinterpol{}"
    elif [[ "$smtSolver" == "verit" ]]; then
        smtSolverLatex="\verit{}"
    elif [[ "$smtSolver" == "z3" ]]; then
        smtSolverLatex="\zthree{}"
    fi

    echo "        & $smtSolverLatex"
    echo "            & $count_sat"
    echo "            & $count_unsat"
    echo "            & $count_unknown"
    echo "            & $count_timeout"
    echo "            & $count_memout"
    echo "            & $count_problem"
    echo "            & $count_unsupported \\\\"
fi
