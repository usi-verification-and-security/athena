#!/bin/bash

chcSolver="$1" # eldarica, golem, spacer
target="$2"    # test, LIA-lin, LIA-nonlin, LIA-Arrays-lin, LIA-Arrays-nonlin

if [[ "$#" -ne 2 ]]; then
  echo "Usage: $0 chcSolver target"
  exit 1
fi

if [[ "$chcSolver" != "eldarica" && "$chcSolver" != "golem" && "$chcSolver" != "spacer" ]]; then
    echo "solver invalid: use eldarica, golem, or spacer"
    exit 1
fi

if [[ "$target" != "test" && "$target" != "LIA-lin" && "$target" != "LIA-nonlin" && "$target" != "LIA-Arrays-lin" && "$target" != "LIA-Arrays-nonlin" ]]; then
    echo "target invalid: use test, LIA-lin, LIA-nonlin, LIA-Arrays-lin, or LIA-Arrays-nonlin"
    exit 1
fi

#########################

cd "$(dirname "$0")" # script's folder

if !(test -d "../results/witnesses_${chcSolver}_$target"); then exit 0; fi
cd ../results/witnesses_${chcSolver}_$target

#########################

function delete_result_smt_checker () {
    # $1 smtChecker
    # $2 smtSolver

    rm -f _results_smt_checker_${1}_smt_solver_${2}.stats
    # TODO also remove files inside each benchmark folder
}

#########################

function log_result_smt_checker () {
    # $1 directory
    # $2 smtChecker
    # $3 smtSolver

    benchmarkDirectory=${1:2}
    cd $benchmarkDirectory

    if test -f "_results_smt_checker_${2}_smt_solver_${3}.stats"; then
        if [[ $(wc -w < "_results_smt_checker_${2}_smt_solver_${3}.stats") -gt 0 ]]; then
            cd ../..
            cd result_${3}_proof_${target}_$chcSolver

            numOfInstances=0

            for instanceDirectory in `find . -type d -name "${benchmarkDirectory}_*"` # iterating over the directories
            do
                numOfInstances=$((numOfInstances+1))
            done

            cd ..
            cd witnesses_${chcSolver}_$target/$benchmarkDirectory

            numOfLines=$(wc -l < _results_smt_checker_${2}_smt_solver_${3}.stats)
            numOfOK=$(grep -o verified _results_smt_checker_${2}_smt_solver_${3}.stats | wc -l)

            numOfHoley=$(grep -o holey _results_smt_checker_${2}_smt_solver_${3}.stats | wc -l)
            numOfHoleyAndOK=$((numOfHoley+numOfOK))

            if [[ "$numOfLines" -lt "$numOfInstances" ]]; then
                echo "$benchmarkDirectory unsupported" >> ../_results_smt_checker_${2}_smt_solver_${3}.stats
            elif [[ "$numOfOK" == "$numOfInstances" ]]; then
                echo "$benchmarkDirectory valid" >> ../_results_smt_checker_${2}_smt_solver_${3}.stats
            elif [[ "$numOfHoleyAndOK" == "$numOfInstances" ]]; then
                echo "$benchmarkDirectory holey" >> ../_results_smt_checker_${2}_smt_solver_${3}.stats
            elif grep -Fqwo "invalid" _results_smt_checker_${2}_smt_solver_${3}.stats; then
                echo "$benchmarkDirectory invalid" >> ../_results_smt_checker_${2}_smt_solver_${3}.stats
            elif grep -Fqwo "unknown" _results_smt_checker_${2}_smt_solver_${3}.stats; then
                echo "$benchmarkDirectory unknown" >> ../_results_smt_checker_${2}_smt_solver_${3}.stats
            elif grep -Fqwo "error" _results_smt_checker_${2}_smt_solver_${3}.stats; then
                echo "$benchmarkDirectory error" >> ../_results_smt_checker_${2}_smt_solver_${3}.stats
            elif grep -Fqwo "memout" _results_smt_checker_${2}_smt_solver_${3}.stats; then
                echo "$benchmarkDirectory memout" >> ../_results_smt_checker_${2}_smt_solver_${3}.stats
            elif grep -Fqwo "timeout" _results_smt_checker_${2}_smt_solver_${3}.stats; then
                echo "$benchmarkDirectory timeout" >> ../_results_smt_checker_${2}_smt_solver_${3}.stats
            else
                echo "$benchmarkDirectory uncategorized" >> ../_results_smt_checker_${2}_smt_solver_${3}.stats
            fi
        fi
    fi

    cd ..
}

#########################

for d in `find . -type d -name '*.smt2'` # iterating over the directories
do
    delete_result_smt_checker "alfc" "cvc5-aletheLF"
    delete_result_smt_checker "carcara" "cvc5-alethe"
    delete_result_smt_checker "lfsc" "cvc5-lfsc"
    delete_result_smt_checker "smtinterpol-checker" "smtinterpol"
    delete_result_smt_checker "tswc" "opensmt"
done

for d in `find . -type d -name '*.smt2'` # iterating over the directories
do
    echo "Logging $1 results with smt checkers for ${d:2}"

    log_result_smt_checker $d "alfc" "cvc5-aletheLF"
    log_result_smt_checker $d "carcara" "cvc5-alethe"
    log_result_smt_checker $d "lfsc" "cvc5-lfsc"
    log_result_smt_checker $d "smtinterpol-checker" "smtinterpol"
    log_result_smt_checker $d "tswc" "opensmt"
done
