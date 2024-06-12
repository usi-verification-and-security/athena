#!/bin/bash

smtSolver="$1" # all, none, cvc5, opensmt, smtinterpol, verit, z3
smtMode="$2"   # all, proof, noProof
target="$3"    # all, test, LIA-lin, LIA-nonlin, LIA-Arrays-lin, LIA-Arrays-nonlin
threads="$4"   # e.g. 16

if [[ "$#" -ne 4 ]]; then
  echo "Usage: $0 smtSolver smtMode target threads"
  exit 1
fi

if [[ "$smtSolver" != "all" && "$smtSolver" != "none" && "$smtSolver" != "cvc5" && "$smtSolver" != "opensmt" && "$smtSolver" != "smtinterpol" && "$smtSolver" != "verit" && "$smtSolver" != "z3" ]]; then
    echo "smtSolver invalid: use all, none, cvc5, opensmt, smtinterpol, verit, or z3"
    exit 1
fi

if [[ "$smtMode" != "all" && "$smtMode" != "proof" && "$smtMode" != "noProof" ]]; then
    echo "smtMode invalid: use all, proof, or noProof"
    exit 1
fi

if [[ "$target" != "all" && "$target" != "test" && "$target" != "LIA-lin" && "$target" != "LIA-nonlin" ]]; then
    echo "target invalid: use all, test, LIA-lin, LIA-nonlin, LIA-Arrays-lin, or LIA-Arrays-nonlin"
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

    if [ -d "results/witnesses_${4}_$3" ]; then
        rm -rf "results/result_${2}_${1}_${3}_$4"; mkdir "results/result_${2}_${1}_${3}_$4"

        for d in results/witnesses_${4}_$3/*; do
            if [ -d "$d" ]; then rm -rf "$d/_results_smt_solver_${2}_${1}.stats"; fi
        done

        if [[ "$1" == "proof" ]]; then
            smtChecker="none"
            if [[ "$2" == "opensmt" ]]; then
                smtChecker="tswc"
            elif [[ "$2" == "cvc5-lfsc" ]]; then
                smtChecker="lfsc"
            elif [[ "$2" == "cvc5-alethe" ]]; then
                smtChecker="carcara"
            elif [[ "$2" == "cvc5-aletheLF" ]]; then
                smtChecker="alfc"
            elif [[ "$2" == "smtinterpol" ]]; then
                smtChecker="smtinterpol-checker"
            fi

            if [[ "$smtChecker" != "none" ]]; then
                rm -rf "results/result_${smtChecker}_${3}_${2}_$4"; mkdir "results/result_${smtChecker}_${3}_${2}_$4"
            fi

            for d in results/witnesses_${4}_$3/*; do
                if [ -d "$d" ]; then rm -rf "$d/_results_smt_solver_${2}_smt_checker_${smtChecker}.stats"; fi
            done
        fi
    fi
}

function delete_by_chcSolver () {
    # $1 smtMode
    # $2 smtSolver
    # $3 target

    delete_folder $1 $2 $3 "eldarica"
    delete_folder $1 $2 $3 "golem"
    delete_folder $1 $2 $3 "spacer"
}

function delete_by_target () {
    # $1 smtMode
    # $2 smtSolver

    if [[ "$target" == "all" ]]; then
        delete_by_chcSolver $1 $2 "LIA-lin"
        delete_by_chcSolver $1 $2 "LIA-nonlin"
        delete_by_chcSolver $1 $2 "LIA-Arrays-lin"
        delete_by_chcSolver $1 $2 "LIA-Arrays-nonlin"
    else
        delete_by_chcSolver $1 $2 $target
    fi
}

function delete_by_smtSolver () {
    # $1 smtMode

    if [[ "$smtSolver" == "all" && "$1" == "proof" ]]; then
        delete_by_target $1 "cvc5-lfsc"
        delete_by_target $1 "cvc5-alethe"
        delete_by_target $1 "cvc5-aletheLF"
        delete_by_target $1 "opensmt"
        delete_by_target $1 "smtinterpol"
        delete_by_target $1 "verit"
        delete_by_target $1 "z3"
    elif [[ "$smtSolver" == "all" && "$1" == "noProof" ]]; then
        delete_by_target $1 "cvc5"
        delete_by_target $1 "opensmt"
        delete_by_target $1 "smtinterpol"
        delete_by_target $1 "verit"
        delete_by_target $1 "z3"
    elif [[ "$smtSolver" == "cvc5" && "$1" == "proof" ]]; then
        delete_by_target $1 "cvc5-lfsc"
        delete_by_target $1 "cvc5-alethe"
        delete_by_target $1 "cvc5-aletheLF"
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

    if [ -d "results/witnesses_${4}_$3" ]; then
        echo "---------------- Running $2 in $1 mode with $3 from $4 ----------------"

        cd "results/witnesses_${4}_$3"
        rm -f "run_${2}_${1}_${3}_$4.calls"

        for f in `find . -type d -name '*.smt2'` # iterating over the directories
        do
            if grep -Fqw "${f:2}" _sat_chc_solver.stats; then
                cd $f

                smtTheory="none"
                if [[ "$3" == "test" ]]; then
                    if grep -Fqw "(forall" $f.out_chc_solver || grep -Fqw "(exists" $f.out_chc_solver; then
                        smtTheory="LIA"
                    else
                        smtTheory="QF_LIA"
                    fi
                elif [[ "$3" == "LIA-lin" || "$3" == "LIA-nonlin" ]]; then
                    if grep -Fqw "(forall" $f.out_chc_solver || grep -Fqw "(exists" $f.out_chc_solver; then
                        smtTheory="LIA"
                    else
                        smtTheory="QF_LIA"
                    fi
                elif [[ "$3" == "LIA-Arrays-lin" || "$3" == "LIA-Arrays-nonlin" ]]; then
                    if grep -Fqw "(forall" $f.out_chc_solver || grep -Fqw "(exists" $f.out_chc_solver; then
                        smtTheory="ALIA"
                    else
                        smtTheory="QF_ALIA"
                    fi
                fi

                python3 ../../../scripts/generate_chc_witness_checks.py ../../../benchmarks/$3/${f:2} ${f:2}.out_chc_solver $smtTheory # the python script runs from the current directory

                for g in `find . -type f -name '*.smt2'`
                do
                    echo "../../scripts/run_smt_solver.sh ${f:2} ${g:2} $3 $2 $1 $4" >> "../run_${2}_${1}_${3}_$4.calls"
                done

                rm -f "_results_smt_solver_${2}_${1}.stats"

                cd ..
            fi
        done

        if [ -s "run_${2}_${1}_${3}_$4.calls" ]; then
            parallel -j $threads < "run_${2}_${1}_${3}_$4.calls"
        else
            echo "No $3 $4 models to be validated"
        fi

        rm -f "run_${2}_${1}_${3}_$4.calls"

        cd ../..
    else
        echo "---------------- No witnesses with $3 from $4 ----------------"
    fi
}

function run_by_chcSolver () {
    # $1 smtMode
    # $2 smtSolver
    # $3 target

    run_file $1 $2 $3 "eldarica"
    run_file $1 $2 $3 "golem"
    run_file $1 $2 $3 "spacer"
}

function run_by_target () {
    # $1 smtMode
    # $2 smtSolver

    if [[ "$target" == "all" ]]; then
        run_by_chcSolver $1 $2 "LIA-lin"
        run_by_chcSolver $1 $2 "LIA-nonlin"
        run_by_chcSolver $1 $2 "LIA-Arrays-lin"
        run_by_chcSolver $1 $2 "LIA-Arrays-nonlin"
    else
        run_by_chcSolver $1 $2 $target
    fi
}

function run_by_smtSolver () {
    # $1 smtMode

    if [[ "$smtSolver" == "all" && "$1" == "proof" ]]; then
        run_by_target $1 "cvc5-lfsc"
        run_by_target $1 "cvc5-alethe"
        run_by_target $1 "cvc5-aletheLF"
        run_by_target $1 "opensmt"
        run_by_target $1 "smtinterpol"
        run_by_target $1 "verit"
        run_by_target $1 "z3"        
    elif [[ "$smtSolver" == "all" && "$1" == "noProof" ]]; then
        run_by_target $1 "cvc5"
        run_by_target $1 "opensmt"
        run_by_target $1 "smtinterpol"
        run_by_target $1 "verit"
        run_by_target $1 "z3"
    elif [[ "$smtSolver" == "cvc5" && "$1" == "proof" ]]; then
        run_by_target $1 "cvc5-lfsc"
        run_by_target $1 "cvc5-alethe"
        run_by_target $1 "cvc5-aletheLF"
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
