#!/bin/bash

smtSolver="$1" # cvc5, cvc5-lfsc, cvc5-alethe, cvc5-aletheLF, opensmt, smtinterpol, verit, z3
smtMode="$2"   # proof, noProof
target="$3"    # test, LIA-lin, LIA-nonlin, LIA-Arrays-lin, LIA-Arrays-nonlin
chcSolver="$4" # eldarica, golem, spacer

if [[ "$#" -ne 4 ]]; then
  echo "Usage: $0 smtSolver smtMode target chcSolver"
  exit 1
fi

if [[ "$smtSolver" != "cvc5" && "$smtSolver" != "cvc5-lfsc" && "$smtSolver" != "cvc5-alethe" && "$smtSolver" != "cvc5-aletheLF" && "$smtSolver" != "opensmt" && "$smtSolver" != "smtinterpol" && "$smtSolver" != "verit"  && "$smtSolver" != "z3" ]]; then
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

#########################

cd "$(dirname "$0")" # script's folder

if !(test -d "../results/result_${smtSolver}_${smtMode}_${target}_$chcSolver"); then exit 0; fi
cd ../results/result_${smtSolver}_${smtMode}_${target}_$chcSolver

#########################

function log_output () {
    rm -f _runtime_${smtSolver}_${smtMode}_${target}_$chcSolver.dataPoints
    rm -f _memory-use_${smtSolver}_${smtMode}_${target}_$chcSolver.dataPoints

    if test -f "_unsat_smt_solver.stats"; then
        if [[ $(wc -w < "_unsat_smt_solver.stats") -gt 0 ]]; then
            while IFS= read -r line; do
                index=0
                for word in $line; do
                    if [[ "$index" -eq 0 ]]; then # instance path
                        file=$word
                        echo "Logging $target unsat output for $smtSolver in $smtMode mode from $chcSolver: $file"
                    elif [[ "$index" -eq 1 ]]; then # runtime
                        runtime=$word
                    elif [[ "$index" -eq 2 ]]; then # memoryUse
                        memoryUse=$word

                        echo "$file unsat $runtime"   >> _runtime_${smtSolver}_${smtMode}_${target}_$chcSolver.dataPoints
                        echo "$file unsat $memoryUse" >> _memory-use_${smtSolver}_${smtMode}_${target}_$chcSolver.dataPoints
                    fi
                    index=$((index+1))
                done
            done < "_unsat_smt_solver.stats"
        fi
    fi

    if test -f "_sat_smt_solver.stats"; then
        if [[ $(wc -w < "_sat_smt_solver.stats") -gt 0 ]]; then
            while IFS= read -r line; do
                index=0
                for word in $line; do
                    if [[ "$index" -eq 0 ]]; then # instance path
                        file=$word
                        echo "Logging $target sat output for $smtSolver in $smtMode mode from $chcSolver: $file"
                    elif [[ "$index" -eq 1 ]]; then # runtime
                        runtime=$word
                    elif [[ "$index" -eq 2 ]]; then # memoryUse
                        memoryUse=$word

                        echo "$file sat $runtime"   >> _runtime_${smtSolver}_${smtMode}_${target}_$chcSolver.dataPoints
                        echo "$file sat $memoryUse" >> _memory-use_${smtSolver}_${smtMode}_${target}_$chcSolver.dataPoints
                    fi
                    index=$((index+1))
                done
            done < "_sat_smt_solver.stats"
        fi
    fi

    if test -f "_unknown_smt_solver.stats"; then
        if [[ $(wc -w < "_unknown_smt_solver.stats") -gt 0 ]]; then
            while IFS= read -r line; do
                index=0
                for word in $line; do
                    if [[ "$index" -eq 0 ]]; then # instance path
                        file=$word
                        echo "Logging $target unknown output for $smtSolver in $smtMode mode from $chcSolver: $file"
                    elif [[ "$index" -eq 1 ]]; then # runtime
                        runtime=$word
                    elif [[ "$index" -eq 2 ]]; then # memoryUse
                        memoryUse=$word

                        echo "$file unknown $runtime"   >> _runtime_${smtSolver}_${smtMode}_${target}_$chcSolver.dataPoints
                        echo "$file unknown $memoryUse" >> _memory-use_${smtSolver}_${smtMode}_${target}_$chcSolver.dataPoints
                    fi
                    index=$((index+1))
                done
            done < "_unknown_smt_solver.stats"
        fi
    fi

    if test -f "_timeout_smt_solver.stats"; then
        if [[ $(wc -w < "_timeout_smt_solver.stats") -gt 0 ]]; then
            while IFS= read -r line; do
                index=0
                for word in $line; do
                    if [[ "$index" -eq 0 ]]; then # instance path
                        file=$word
                        echo "Logging $target timeout output for $smtSolver in $smtMode mode from $chcSolver: $file"
                    elif [[ "$index" -eq 1 ]]; then # runtime
                        runtime=$word
                    elif [[ "$index" -eq 2 ]]; then # memoryUse
                        memoryUse=$word

                        echo "$file tOut $runtime"   >> _runtime_${smtSolver}_${smtMode}_${target}_$chcSolver.dataPoints
                        echo "$file tOut $memoryUse" >> _memory-use_${smtSolver}_${smtMode}_${target}_$chcSolver.dataPoints
                    fi
                    index=$((index+1))
                done
            done < "_timeout_smt_solver.stats"
        fi
    fi

    if test -f "_memout_smt_solver.stats"; then
        if [[ $(wc -w < "_memout_smt_solver.stats") -gt 0 ]]; then
            while IFS= read -r line; do
                index=0
                for word in $line; do
                    if [[ "$index" -eq 0 ]]; then # instance path
                        file=$word
                        echo "Logging $target memeout output for $smtSolver in $smtMode mode from $chcSolver: $file"
                    elif [[ "$index" -eq 1 ]]; then # runtime
                        runtime=$word
                    elif [[ "$index" -eq 2 ]]; then # memoryUse
                        memoryUse=$word

                        echo "$file mOut $runtime"   >> _runtime_${smtSolver}_${smtMode}_${target}_$chcSolver.dataPoints
                        echo "$file mOut $memoryUse" >> _memory-use_${smtSolver}_${smtMode}_${target}_$chcSolver.dataPoints
                    fi
                    index=$((index+1))
                done
            done < "_memout_smt_solver.stats"
        fi
    fi
}

#########################

log_output
