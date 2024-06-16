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

function delete_result_smt_solver () {
    # $1 smtSolver
    # $2 smtMode

    rm -f _results_smt_solver_${1}_${2}.stats
    # TODO also remove files inside each benchmark folder
}

#########################

function log_result_smt_solver () {
    # $1 directory
    # $2 smtSolver
    # $3 smtMode

    benchmarkDirectory=${1:2}
    cd $benchmarkDirectory

    if test -f "_results_smt_solver_${2}_${3}.stats"; then
        if [[ $(wc -w < "_results_smt_solver_${2}_${3}.stats") -gt 0 ]]; then
            cd ../..
            cd result_${2}_${3}_${target}_$chcSolver

            numOfInstances=0

            for instanceDirectory in `find . -type d -name "${benchmarkDirectory}_*"` # iterating over the directories
            do
                numOfInstances=$((numOfInstances+1))
            done

            cd ..
            cd witnesses_${chcSolver}_$target/$benchmarkDirectory

            numOfOK=$(grep -o unsat _results_smt_solver_${2}_${3}.stats | wc -l)

            if [[ "$numOfOK" == "$numOfInstances" ]]; then
                echo "$benchmarkDirectory valid" >> ../_results_smt_solver_${2}_${3}.stats
            elif grep -Fqwo "sat" _results_smt_solver_${2}_${3}.stats; then
                echo "$benchmarkDirectory invalid" >> ../_results_smt_solver_${2}_${3}.stats
            elif grep -Fqwo "unknown" _results_smt_solver_${2}_${3}.stats; then
                echo "$benchmarkDirectory unknown" >> ../_results_smt_solver_${2}_${3}.stats
            elif grep -Fqwo "error" _results_smt_solver_${2}_${3}.stats; then
                echo "$benchmarkDirectory error" >> ../_results_smt_solver_${2}_${3}.stats
            elif grep -Fqwo "unsupported" _results_smt_solver_${2}_${3}.stats; then
                echo "$benchmarkDirectory unsupported" >> ../_results_smt_solver_${2}_${3}.stats
            elif grep -Fqwo "memout" _results_smt_solver_${2}_${3}.stats; then
                echo "$benchmarkDirectory memout" >> ../_results_smt_solver_${2}_${3}.stats
            elif grep -Fqwo "timeout" _results_smt_solver_${2}_${3}.stats; then
                echo "$benchmarkDirectory timeout" >> ../_results_smt_solver_${2}_${3}.stats
            else
                echo "$benchmarkDirectory uncategorized" >> ../_results_smt_solver_${2}_${3}.stats
            fi
        fi
    fi

    cd ..
}

#########################

for d in `find . -type d -name '*.smt2'` # iterating over the directories
do
    delete_result_smt_solver "cvc5" "noProof"
    delete_result_smt_solver "opensmt" "noProof"
    delete_result_smt_solver "smtinterpol" "noProof"
    delete_result_smt_solver "verit" "noProof"
    delete_result_smt_solver "z3" "noProof"

    delete_result_smt_solver "cvc5-lfsc" "proof"
    delete_result_smt_solver "cvc5-alethe" "proof"
    delete_result_smt_solver "cvc5-aletheLF" "proof"
    delete_result_smt_solver "opensmt" "proof"
    delete_result_smt_solver "smtinterpol" "proof"
    delete_result_smt_solver "verit" "proof"
    delete_result_smt_solver "z3" "proof"
done

for d in `find . -type d -name '*.smt2'` # iterating over the directories
do
    echo "Logging $1 results with smt solvers for ${d:2}"

    log_result_smt_solver $d "cvc5" "noProof"
    log_result_smt_solver $d "opensmt" "noProof"
    log_result_smt_solver $d "smtinterpol" "noProof"
    log_result_smt_solver $d "verit" "noProof"
    log_result_smt_solver $d "z3" "noProof"

    log_result_smt_solver $d "cvc5-lfsc" "proof"
    log_result_smt_solver $d "cvc5-alethe" "proof"
    log_result_smt_solver $d "cvc5-aletheLF" "proof"
    log_result_smt_solver $d "opensmt" "proof"
    log_result_smt_solver $d "smtinterpol" "proof"
    log_result_smt_solver $d "verit" "proof"
    log_result_smt_solver $d "z3" "proof"
done
