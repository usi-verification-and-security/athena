#!/bin/bash

smtSolver="$1" # all, none, opensmt, z3, verit, cvc5, smtinterpol
smtMode="$2"   # all, proof, noProof
target="$3"    # all, test, LIA-lin, LIA-nonlin
threads="$4"   # e.g. 16

if [[ "$#" -ne 4 ]]; then
  echo "Usage: $0 smtSolver smtMode target threads"
  exit 1
fi

if [[ "$smtSolver" != "all" && "$smtSolver" != "none" && "$smtSolver" != "opensmt" && "$smtSolver" != "z3" && "$smtSolver" != "verit" && "$smtSolver" != "cvc5" && "$smtSolver" != "smtinterpol" ]]; then
    echo "smtSolver invalid: use all, none, opensmt, z3, verit, cvc5, or smtinterpol"
    exit 1
fi

if [[ "$smtMode" != "all" && "$smtMode" != "proof" && "$smtMode" != "noProof" ]]; then
    echo "smtMode invalid: use all, proof, or noProof"
    exit 1
fi

if [[ "$target" != "all" && "$target" != "test" && "$target" != "LIA-lin" && "$target" != "LIA-nonlin" ]]; then
    echo "target invalid: use all, test, LIA-lin, or LIA-nonlin"
    exit 1
fi

if [[ "$threads" -eq 0 ]]; then
    echo "Number of threads invalid"
    exit 1
fi

#########################

function delete_folder () {
    # $1 smtMode
    # $2 smtSolver
    # $3 target
    # $4 chcSolver

    rm -rf "results/result_${2}_${1}_${3}_$4"; mkdir "results/result_${2}_${1}_${3}_$4"

    if [[ "$1" == "proof" ]]; then
        smtChecker="none"
        if [[ "$2" == "opensmt" ]]; then
            smtChecker="tswc"
        elif [[ "$2" == "cvc5-lfsc" ]]; then
            smtChecker="lfsc"
        elif [[ "$2" == "cvc5-alethe" ]]; then
            smtChecker="carcara"
        elif [[ "$2" == "smtinterpol" ]]; then
            smtChecker="smtinterpol-checker"
        fi

        if [[ "$smtChecker" != "none" ]]; then
            rm -rf "results/result_${smtChecker}_${3}_${2}_$4"; mkdir "results/result_${smtChecker}_${3}_${2}_$4"
        fi
    fi
}

function delete_by_chcSolver () {
    # $1 smtMode
    # $2 smtSolver
    # $3 target

    delete_folder $1 $2 $3 "golem"
    delete_folder $1 $2 $3 "eldarica"
    delete_folder $1 $2 $3 "spacer"
}

function delete_by_target () {
    # $1 smtMode
    # $2 smtSolver

    if [[ "$target" == "all" ]]; then
        delete_by_chcSolver $1 $2 "LIA-lin"
        delete_by_chcSolver $1 $2 "LIA-nonlin"
    else
        delete_by_chcSolver $1 $2 $target
    fi
}

function delete_by_smtSolver () {
    # $1 smtMode

    if [[ "$smtSolver" == "all" && "$1" == "proof" ]]; then
        delete_by_target $1 "opensmt"
        delete_by_target $1 "z3"
        delete_by_target $1 "verit"
        delete_by_target $1 "cvc5-lfsc"
        delete_by_target $1 "cvc5-alethe"
        delete_by_target $1 "smtinterpol"
    elif [[ "$smtSolver" == "all" && "$1" == "noProof" ]]; then
        delete_by_target $1 "opensmt"
        delete_by_target $1 "z3"
        delete_by_target $1 "verit"
        delete_by_target $1 "cvc5"
        delete_by_target $1 "smtinterpol"
    elif [[ "$smtSolver" == "cvc5" && "$1" == "proof" ]]; then
        delete_by_target $1 "cvc5-lfsc"
        delete_by_target $1 "cvc5-alethe"
    elif [[ "$smtSolver" != "none" ]]; then
        delete_by_target $1 $smtSolver
    fi
}

function delete_by_mode () {
    if [[ "$smtMode" == "all" ]]; then
        delete_by_smtSolver "proof"
        delete_by_smtSolver "noProof"
    else
        delete_by_smtSolver $smtMode
    fi
}

function delete_results () {
    delete_by_mode
}

#########################

function run_file () {
    # $1 smtMode
    # $2 smtSolver
    # $3 target
    # $4 chcSolver

    echo "---------- Running $2 in $1 mode with $3 from $4 ----------"

    cd "results/witnesses_${4}_$3"
    rm -f "run_${2}_${1}_${3}_$4.calls"

    smtTheory="none"
    if [[ "$3" == "test" ]]; then
        smtTheory="QF_LIA"
    elif [[ "$3" == "LIA-lin" || "$3" == "LIA-nonlin" ]]; then
        smtTheory="QF_LIA"
    fi

    for f in `find . -type d -name '*.smt2'`
    do
        if grep -Fqw "${f:2}" _sat_chc_solver.stats; then
            cd $f
            
            python3 ../../../scripts/generate_chc_witness_checks.py ../../../benchmarks/$3/${f:2} ${f:2}.out_chc_solver $smtTheory # the python script runs from the current directory

            for g in `find . -type f -name '*.smt2'`
            do
                echo "../../scripts/run_smt_solver.sh ${f:2} ${g:2} $3 $2 $1 $4" >> "../run_${2}_${1}_${3}_$4.calls"
            done

            cd ..
        fi
    done

    parallel -j $threads < "run_${2}_${1}_${3}_$4.calls"
    rm -f "run_${2}_${1}_${3}_$4.calls"

    cd ../..
}

function run_by_chcSolver () {
    # $1 smtMode
    # $2 smtSolver
    # $3 target

    run_file $1 $2 $3 "golem"
    run_file $1 $2 $3 "eldarica"
    run_file $1 $2 $3 "spacer"
}

function run_by_target () {
    # $1 smtMode
    # $2 smtSolver

    if [[ "$target" == "all" ]]; then
        run_by_chcSolver $1 $2 "LIA-lin"
        run_by_chcSolver $1 $2 "LIA-nonlin"
    else
        run_by_chcSolver $1 $2 $target
    fi
}

function run_by_smtSolver () {
    # $1 smtMode

    if [[ "$smtSolver" == "all" && "$1" == "proof" ]]; then
        run_by_target $1 "opensmt"
        run_by_target $1 "z3"
        run_by_target $1 "verit"
        run_by_target $1 "cvc5-lfsc"
        run_by_target $1 "cvc5-alethe"
        run_by_target $1 "smtinterpol"
    elif [[ "$smtSolver" == "all" && "$1" == "noProof" ]]; then
        run_by_target $1 "opensmt"
        run_by_target $1 "z3"
        run_by_target $1 "verit"
        run_by_target $1 "cvc5"
        run_by_target $1 "smtinterpol"
    elif [[ "$smtSolver" == "cvc5" && "$1" == "proof" ]]; then
        run_by_target $1 "cvc5-lfsc"
        run_by_target $1 "cvc5-alethe"
    elif [[ "$smtSolver" != "none" ]]; then
        run_by_target $1 $smtSolver
    fi
}

function run_by_mode () {
    if [[ "$smtMode" == "all" ]]; then
        run_by_smtSolver "proof"
        run_by_smtSolver "noProof"
    else
        run_by_smtSolver $smtMode
    fi
}

function run_benchmarks () {
    run_by_mode
}

#########################

cd "$(dirname "$0")" # script's folder
cd ..

delete_results
run_benchmarks