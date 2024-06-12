#!/bin/bash

smtChecker="$1" # alfc, carcara, lfsc, smtinterpol-checker, tswc
smtSolver="$2"  # cvc5-lfsc, cvc5-alethe, cvc5-aletheLF, opensmt, smtinterpol, verit, z3
target="$3"     # test, LIA-lin, LIA-nonlin, LIA-Arrays-lin, LIA-Arrays-nonlin
chcSolver="$4"  # eldarica, golem, spacer

if [[ "$#" -ne 4 ]]; then
  echo "Usage: $0 smtChecker smtSolver target chcSolver"
  exit 1
fi

if [[ "$smtSolver" != "cvc5-lfsc" && "$smtSolver" != "cvc5-alethe" && "$smtSolver" != "cvc5-aletheLF" && "$smtSolver" != "opensmt" && "$smtSolver" != "smtinterpol" && "$smtSolver" != "verit" && "$smtSolver" != "z3" ]]; then
    echo "smtSolver invalid: use cvc5-lfsc, cvc5-alethe, cvc5-aletheLF, opensmt, smtinterpol, verit, or z3"
    exit 1
fi

if [[ "$smtChecker" != "alfc" && "$smtChecker" != "carcara" && "$smtChecker" != "lfsc" && "$smtChecker" != "smtinterpol-checker" && "$smtChecker" != "tswc" ]]; then
    echo "smtChecker invalid: use alfc, carcara, lfsc, smtinterpol-checker, or tswc"
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
