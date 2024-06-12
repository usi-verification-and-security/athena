#!/bin/bash

chcSolver="$1" # all, none, eldarica, golem, spacer
target="$2"    # all, test, LIA-lin, LIA-nonlin, LIA-Arrays-lin, LIA-Arrays-nonlin
threads="$3"   # e.g. 16

if [[ "$#" -ne 3 ]]; then
  echo "Usage: $0 chcSolver target threads"
  exit 1
fi

if [[ "$chcSolver" != "all" && "$chcSolver" != "none" && "$chcSolver" != "eldarica" && "$chcSolver" != "golem" && "$chcSolver" != "spacer" ]]; then
    echo "chcSolver invalid: use all, none, eldarica, golem, or spacer"
    exit 1
fi

if [[ "$target" != "all" && "$target" != "test" && "$target" != "LIA-lin" && "$target" != "LIA-nonlin" && "$target" != "LIA-Arrays-lin" && "$target" != "LIA-Arrays-nonlin" ]]; then
    echo "target invalid: use all, test, LIA-lin, LIA-nonlin, LIA-Arrays-lin, or LIA-Arrays-nonlin"
    exit 1
fi

if [[ "$threads" -eq 0 ]]; then
    echo "Number of threads invalid"
    exit 1
fi

#########################

function delete_folder () {
    # $1 chcSolver
    # $2 target

    rm -rf "results/witnesses_${1}_$2"; mkdir "results/witnesses_${1}_$2"
    if [[ "$1" != "golem" || ("$2" != "LIA-Arrays-lin" && "$2" != "LIA-Arrays-nonlin") ]]; then # golem does not support arrays
        touch results/witnesses_${1}_$2/_sat_chc_solver.stats # required for evaluate_smt_solver.sh
    fi
}

function delete_by_target () {
    # $1 chcSolver

    if [[ "$target" == "all" ]]; then
        delete_folder $1 "LIA-lin"
        delete_folder $1 "LIA-nonlin"
        delete_folder $1 "LIA-Arrays-lin"
        delete_folder $1 "LIA-Arrays-nonlin"
    else
        delete_folder $1 $target
    fi
}

function delete_by_chcSolver () {
    if [[ "$chcSolver" == "all" ]]; then
        delete_by_target "eldarica"
        delete_by_target "golem"
        delete_by_target "spacer"
    elif [[ "$chcSolver" != "none" ]]; then
        delete_by_target $chcSolver
    fi
}

function delete_results () {
    delete_by_chcSolver
}

#########################

function run_file () {
    # $1 chcSolver
    # $2 target

    echo "---------------- Running $1 with $2 ----------------"

    cd "benchmarks/$2"
    rm -f "run_${1}_$2.calls"

    for f in `find . -type f -name '*.smt2'`; do echo "../../scripts/run_chc_solver.sh ${f:2} $2 $1"; done > "run_${1}_$2.calls"
    parallel -j $threads < "run_${1}_$2.calls"
    rm -f "run_${1}_$2.calls"

    cd ../..
}

function run_by_target () {
    # $1 chcSolver

    if [[ "$target" == "all" ]]; then
        run_file $1 "LIA-lin"
        run_file $1 "LIA-nonlin"
        run_file $1 "LIA-Arrays-lin"
        run_file $1 "LIA-Arrays-nonlin"
    else
        run_file $1 $target
    fi
}

function run_by_chcSolver () {
    if [[ "$chcSolver" == "all" ]]; then
        run_by_target "eldarica"
        run_by_target "golem"
        run_by_target "spacer"
    elif [[ "$chcSolver" != "none" ]]; then
        run_by_target $chcSolver
    fi
}

function run_benchmarks () {
    run_by_chcSolver
}

#########################

cd "$(dirname "$0")" # script's folder
cd ..

delete_results
run_benchmarks
