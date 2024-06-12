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

function log_output () {
    rm -f _runtime_${chcSolver}_${target}.dataPoints
    rm -f _memory-use_${chcSolver}_${target}.dataPoints

    if test -f "_unsat_chc_solver.stats"; then
        if [[ $(wc -w < "_unsat_chc_solver.stats") -gt 0 ]]; then
            while IFS= read -r line; do
                index=0
                for word in $line; do
                    if [[ "$index" -eq 0 ]]; then # instance path
                        file=$word
                        echo "Logging $target unsat output for $chcSolver: $file"
                    elif [[ "$index" -eq 1 ]]; then # runtime
                        runtime=$word
                    elif [[ "$index" -eq 2 ]]; then # memoryUse
                        memoryUse=$word

                        echo "$file unsat $runtime"   >> _runtime_${chcSolver}_${target}.dataPoints
                        echo "$file unsat $memoryUse" >> _memory-use_${chcSolver}_${target}.dataPoints
                    fi
                    index=$((index+1))
                done
            done < "_unsat_chc_solver.stats"
        fi
    fi

    if test -f "_sat_chc_solver.stats"; then
        if [[ $(wc -w < "_sat_chc_solver.stats") -gt 0 ]]; then
            while IFS= read -r line; do
                index=0
                for word in $line; do
                    if [[ "$index" -eq 0 ]]; then # instance path
                        file=$word
                        echo "Logging $target sat output for $chcSolver: $file"
                    elif [[ "$index" -eq 1 ]]; then # runtime
                        runtime=$word
                    elif [[ "$index" -eq 2 ]]; then # memoryUse
                        memoryUse=$word

                        echo "$file sat $runtime"   >> _runtime_${chcSolver}_${target}.dataPoints
                        echo "$file sat $memoryUse" >> _memory-use_${chcSolver}_${target}.dataPoints
                    fi
                    index=$((index+1))
                done
            done < "_sat_chc_solver.stats"
        fi
    fi

     if test -f "_unknown_chc_solver.stats"; then
        if [[ $(wc -w < "_unknown_chc_solver.stats") -gt 0 ]]; then
            while IFS= read -r line; do
                index=0
                for word in $line; do
                    if [[ "$index" -eq 0 ]]; then # instance path
                        file=$word
                        echo "Logging $target unknown output for $chcSolver: $file"
                    elif [[ "$index" -eq 1 ]]; then # runtime
                        runtime=$word
                    elif [[ "$index" -eq 2 ]]; then # memoryUse
                        memoryUse=$word

                        echo "$file unknown $runtime"   >> _runtime_${chcSolver}_${target}.dataPoints
                        echo "$file unknown $memoryUse" >> _memory-use_${chcSolver}_${target}.dataPoints
                    fi
                    index=$((index+1))
                done
            done < "_unknown_chc_solver.stats"
        fi
    fi

    if test -f "_timeout_chc_solver.stats"; then
        if [[ $(wc -w < "_timeout_chc_solver.stats") -gt 0 ]]; then
            while IFS= read -r line; do
                index=0
                for word in $line; do
                    if [[ "$index" -eq 0 ]]; then # instance path
                        file=$word
                        echo "Logging $target timeout output for $chcSolver: $file"
                    elif [[ "$index" -eq 1 ]]; then # runtime
                        runtime=$word
                    elif [[ "$index" -eq 2 ]]; then # memoryUse
                        memoryUse=$word

                        echo "$file tOut $runtime"   >> _runtime_${chcSolver}_${target}.dataPoints
                        echo "$file tOut $memoryUse" >> _memory-use_${chcSolver}_${target}.dataPoints
                    fi
                    index=$((index+1))
                done
            done < "_timeout_chc_solver.stats"
        fi
    fi

    if test -f "_memout_chc_solver.stats"; then
        if [[ $(wc -w < "_memout_chc_solver.stats") -gt 0 ]]; then
            while IFS= read -r line; do
                index=0
                for word in $line; do
                    if [[ "$index" -eq 0 ]]; then # instance path
                        file=$word
                        echo "Logging $target memeout output for $chcSolver: $file"
                    elif [[ "$index" -eq 1 ]]; then # runtime
                        runtime=$word
                    elif [[ "$index" -eq 2 ]]; then # memoryUse
                        memoryUse=$word

                        echo "$file mOut $runtime"   >> _runtime_${chcSolver}_${target}.dataPoints
                        echo "$file mOut $memoryUse" >> _memory-use_${chcSolver}_${target}.dataPoints
                    fi
                    index=$((index+1))
                done
            done < "_memout_chc_solver.stats"
        fi
    fi
}

#########################

log_output
