#!/bin/bash

smtChecker="$1" # tswc, lfsc, carcara, smtinterpol-checker
smtSolver="$2"  # opensmt, z3, verit, cvc5, cvc5-lfsc, cvc5-alethe, smtinterpol
target="$3"     # test, LIA-lin, LIA-nonlin
chcSolver="$4"  # golem, eldarica, spacer

if [[ "$#" -ne 4 ]]; then
  echo "Usage: $0 smtChecker smtSolver target chcSolver"
  exit 1
fi

if [[ "$smtSolver" != "opensmt" && "$smtSolver" != "z3" && "$smtSolver" != "verit" && "$smtSolver" != "cvc5" && "$smtSolver" != "cvc5-lfsc" && "$smtSolver" != "cvc5-alethe" && "$smtSolver" != "smtinterpol" ]]; then
    echo "smtSolver invalid: use opensmt, z3, verit, cvc5, cvc5-lfsc, cvc5-alethe, or smtinterpol"
    exit 1
fi

if [[ "$smtChecker" != "tswc" && "$smtChecker" != "lfsc" && "$smtChecker" != "carcara" && "$smtChecker" != "smtinterpol-checker" ]]; then
    echo "smtChecker invalid: use tswc, lfsc, carcara, or smtinterpol-checker"
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

if !(test -d "../results/result_${smtChecker}_${target}_${smtSolver}_$chcSolver"); then exit 0; fi
cd ../results/result_${smtChecker}_${target}_${smtSolver}_$chcSolver

#########################

function log_output () {
    rm -f _runtime_${smtChecker}_${target}_${smtSolver}_$chcSolver.dataPoints
    rm -f _memory-use_${smtChecker}_${target}_${smtSolver}_$chcSolver.dataPoints

    if test -f "_verified_smt_checker.stats"; then
        if [[ $(wc -w < "_verified_smt_checker.stats") -gt 0 ]]; then
            while IFS= read -r line; do
                index=0
                for word in $line; do
                    if [[ "$index" -eq 0 ]]; then # instance path
                        file=$word
                        echo "Logging $target verified output for $smtChecker from $smtSolver and $chcSolver: $file"
                    elif [[ "$index" -eq 1 ]]; then # runtime
                        runtime=$word
                    elif [[ "$index" -eq 2 ]]; then # memoryUse
                        memoryUse=$word

                        echo "$file verified $runtime"   >> _runtime_${smtChecker}_${target}_${smtSolver}_$chcSolver.dataPoints
                        echo "$file verified $memoryUse" >> _memory-use_${smtChecker}_${target}_${smtSolver}_$chcSolver.dataPoints
                    fi
                    index=$((index+1))
                done
            done < "_verified_smt_checker.stats"
        fi
    fi

    if test -f "_invalid_smt_checker.stats"; then
        if [[ $(wc -w < "_invalid_smt_checker.stats") -gt 0 ]]; then
            while IFS= read -r line; do
                index=0
                for word in $line; do
                    if [[ "$index" -eq 0 ]]; then # instance path
                        file=$word
                        echo "Logging $target invalid output for $smtChecker from $smtSolver and $chcSolver: $file"
                    elif [[ "$index" -eq 1 ]]; then # runtime
                        runtime=$word
                    elif [[ "$index" -eq 2 ]]; then # memoryUse
                        memoryUse=$word

                        echo "$file invalid $runtime"   >> _runtime_${smtChecker}_${target}_${smtSolver}_$chcSolver.dataPoints
                        echo "$file invalid $memoryUse" >> _memory-use_${smtChecker}_${target}_${smtSolver}_$chcSolver.dataPoints
                    fi
                    index=$((index+1))
                done
            done < "_invalid_smt_checker.stats"
        fi
    fi

    if test -f "_timeout_smt_checker.stats"; then
        if [[ $(wc -w < "_timeout_smt_checker.stats") -gt 0 ]]; then
            while IFS= read -r line; do
                index=0
                for word in $line; do
                    if [[ "$index" -eq 0 ]]; then # instance path
                        file=$word
                        echo "Logging $target timeout output for $smtChecker from $smtSolver and $chcSolver: $file"
                    elif [[ "$index" -eq 1 ]]; then # runtime
                        runtime=$word
                    elif [[ "$index" -eq 2 ]]; then # memoryUse
                        memoryUse=$word

                        echo "$file tOut $runtime"   >> _runtime_${smtChecker}_${target}_${smtSolver}_$chcSolver.dataPoints
                        echo "$file tOut $memoryUse" >> _memory-use_${smtChecker}_${target}_${smtSolver}_$chcSolver.dataPoints
                    fi
                    index=$((index+1))
                done
            done < "_timeout_smt_checker.stats"
        fi
    fi

    if test -f "_memout_smt_checker.stats"; then
        if [[ $(wc -w < "_memout_smt_checker.stats") -gt 0 ]]; then
            while IFS= read -r line; do
                index=0
                for word in $line; do
                    if [[ "$index" -eq 0 ]]; then # instance path
                        file=$word
                        echo "Logging $target memeout output for $smtChecker from $smtSolver and $chcSolver: $file"
                    elif [[ "$index" -eq 1 ]]; then # runtime
                        runtime=$word
                    elif [[ "$index" -eq 2 ]]; then # memoryUse
                        memoryUse=$word

                        echo "$file mOut $runtime"   >> _runtime_${smtChecker}_${target}_${smtSolver}_$chcSolver.dataPoints
                        echo "$file mOut $memoryUse" >> _memory-use_${smtChecker}_${target}_${smtSolver}_$chcSolver.dataPoints
                    fi
                    index=$((index+1))
                done
            done < "_memout_smt_checker.stats"
        fi
    fi
}

#########################

log_output