#!/bin/bash

timeLimit=1800    # 30 minutes (in seconds)
memLimit=10000000 # 10 GB (in Kbytes)
jvmMemLimit="10g" # 10 GB

file="$1"      # .smt2 file
target="$2"    # test, LIA-lin, LIA-nonlin, LIA-Arrays-lin, LIA-Arrays-nonlin
chcSolver="$3" # eldarica, golem, spacer

if [[ "$#" -ne 3 ]]; then
  echo "Usage: $0 *.smt2 target chcSolver"
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
cd "../results/witnesses_${chcSolver}_$target"

echo "Running $chcSolver with $file"

smtTheory="none" # for golem
if [[ "$target" == "test" ]]; then
    smtTheory="QF_LIA"
elif [[ "$target" == "LIA-lin" || "$target" == "LIA-nonlin" ]]; then
    smtTheory="QF_LIA"
elif [[ "$target" == "LIA-Arrays-lin" || "$target" == "LIA-Arrays-nonlin" ]]; then
    smtTheory="unsupported"
    if [[ "$chcSolver" == "golem" ]]; then # golem does not support arrays
        echo "$target is not supported by $chcSolver, skipping $file"
        exit 0
    fi
fi

mkdir $file
cd $file

cp ../../../benchmarks/$target/$file ./$file

chcSolver_options=""
jvm=""
if [[ "$chcSolver" == "golem" ]]; then
    chcSolver_options="--print-witness --logic $smtTheory"
elif [[ "$chcSolver" == "eldarica" ]]; then
    chcSolver=eld
    chcSolver_options="-ssol"
    jvm="export _JAVA_OPTIONS='-Xmx$jvmMemLimit';"
    sed -i '$ d' $file # remove last line
elif [[ "$chcSolver" == "spacer" ]]; then
    chcSolver=z3
    sed -i '$ d' $file # remove last line
    sed -i '$ d' $file # remove last line
    echo "(check-sat)" >> $file
    echo "(get-model)" >> $file
    echo "(exit)" >> $file
fi

# --format "file runtime(sec) max_memory(Kbytes)"
# runtime is given as userTime+sysTime, it should be equal to the CPU time used by ulimit
# ulimit and jvm memory options conflict with one another, thus the conditional
if [[ "$jvm" == "" ]]; then
    /usr/bin/time --output ../_run_chc_solver.stats --append --format "$file %U+%S %M" sh -c "ulimit -Sv $memLimit; ulimit -St $timeLimit; ../../../binaries/chc_solvers/$chcSolver $chcSolver_options $file" &> $file.out_chc_solver
    exit_status=$?
else
    /usr/bin/time --output ../_run_chc_solver.stats --append --format "$file %U+%S %M" sh -c "ulimit -St $timeLimit; $jvm ../../../binaries/chc_solvers/$chcSolver $chcSolver_options $file" &> $file.out_chc_solver
    exit_status=$?
fi

runtime=$(grep "$file" ../_run_chc_solver.stats | awk '{print $2}') # gets the second string in _run_chc_solver.stats for file
memoryUse=$(grep "$file" ../_run_chc_solver.stats | awk '{print $3}') # gets the third string in _run_chc_solver.stats for file

sed -i '/model is not available/d' $file.out_chc_solver # remove error in output if UNSAT, since we always ask for a witness; only observed in spacer

result="none"
if [[ "$exit_status" -eq 152 ]] || grep -Fqw "interrupted by timeout" $file.out_chc_solver || grep -Fqw "CPU time limit exceeded" $file.out_chc_solver; then # timeout
    echo "$file $runtime $memoryUse" >> ../_timeout_chc_solver.stats
    result="timeout"
elif [[ "$exit_status" -eq 139 ]] || grep -Fqw "out of memory" $file.out_chc_solver || grep -Fqw "Out-of-memory error" $file.out_chc_solver || grep -Fqw "stack overflow" $file.out_chc_solver || grep -Fqw "StackOverflowError" $file.out_chc_solver; then # memout
    echo "$file $runtime $memoryUse" >> ../_memout_chc_solver.stats
    result="memout"
elif grep -Fqw "Predicate generation failed" $file.out_chc_solver || grep -Fqw "Internal exception" $file.out_chc_solver; then # error result; only observed with eldarica
    echo "$file $runtime $memoryUse" >> ../_problem_chc_solver.stats
    result="error"
elif $(grep -m1 ^ $file.out_chc_solver | grep -Fqw "unknown"); then # unknown result; we only check the first line to avoid miscategorizing
    echo "$file $runtime $memoryUse" >> ../_unknown_chc_solver.stats
    result="unknown"
elif grep -Fqw "sat" $file.out_chc_solver; then # SAT result
    echo "$file $runtime $memoryUse" >> ../_sat_chc_solver.stats
    result="sat"
elif grep -Fqw "unsat" $file.out_chc_solver; then # UNSAT result
    echo "$file $runtime $memoryUse" >> ../_unsat_chc_solver.stats
    result="unsat"
else
    echo "$file $runtime $memoryUse" >> ../_uncategorized_chc_solver.stats
    result="uncategorized"
fi

rm $file

if [[ "$chcSolver" == "eld" ]]; then # eldarica
    sed -i '1d' $file.out_chc_solver # remove first line, which contains _JAVA_OPTIONS
    chcSolver="eldarica"
elif [[ "$chcSolver" == "z3" ]]; then # spacer
    if [[ "$result" == "sat" ]]; then # adjust spacer witness formatting
        sed -i '2d' $file.out_chc_solver  # remove second line
        sed -i '$ d' $file.out_chc_solver # remove last line
    fi
    chcSolver="spacer"
fi

if grep -Fqw "(forall" $file.out_chc_solver || grep -Fqw "(exists" $file.out_chc_solver; then
    echo "$file" >> ../_quantifiers_chc_solver.stats # log quantifiers
fi

if [[ "$result" == "sat" ]]; then
    witnessStats=$(wc -c "$file.out_chc_solver") # "size file" string
    witnessStatsArr=(${witnessStats}) # (size, file) array
    witnessSize=${witnessStatsArr[0]} # size in bytes
    witnessName=${witnessStatsArr[1]}
    echo "$witnessName sat $witnessSize" >> ../_witness-size_${chcSolver}_${target}.dataPoints # log witness size
fi
