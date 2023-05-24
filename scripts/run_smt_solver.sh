#!/bin/bash

timeLimit=60     # 1 minute (in seconds)
memLimit=5000000 # 5 GB (in Kbytes)
jvmMemLimit="5g" # 5 GB

chcFileName="$1" # .smt2 file
smtFileName="$2" # .smt2 file
target="$3"      # test, LIA-lin, LIA-nonlin
smtSolver="$4"   # opensmt, z3, verit, cvc5, cvc5-lfsc, cvc5-alethe, smtinterpol
smtMode="$5"     # proof, noProof
chcSolver="$6"   # golem, eldarica, spacer

if [[ "$#" -ne 6 ]]; then
  echo "Usage: $0 *.smt2 *.smt2 target smtSolver smtMode chcSolver"
  exit 1
fi

if [[ "$target" != "test" && "$target" != "LIA-lin" && "$target" != "LIA-nonlin" ]]; then
    echo "target invalid: use test, LIA-lin, or LIA-nonlin"
    exit 1
fi

if [[ "$smtSolver" != "opensmt" && "$smtSolver" != "z3" && "$smtSolver" != "verit" && "$smtSolver" != "cvc5" && "$smtSolver" != "cvc5-lfsc" && "$smtSolver" != "cvc5-alethe" && "$smtSolver" != "smtinterpol" ]]; then
    echo "smtSolver invalid: use opensmt, z3, verit, cvc5, cvc5-lfsc, cvc5-alethe, or smtinterpol"
    exit 1
fi

if [[ "$smtMode" != "proof" && "$smtMode" != "noProof" ]]; then
    echo "smtMode invalid: use proof, or noProof"
    exit 1
fi

if [[ "$chcSolver" != "golem" && "$chcSolver" != "eldarica" && "$chcSolver" != "spacer" ]]; then
    echo "chcSolver invalid: use golem, eldarica, or spacer"
    exit 1
fi

#########################

cd "$(dirname "$0")" # script's folder
cd "../results/result_${smtSolver}_${smtMode}_${target}_$chcSolver"

echo "Running $smtSolver in $smtMode mode with $chcFileName ($smtFileName) from $chcSolver"

smtSolverCmd=$smtSolver
jvm=""
if [[ "$smtSolver" == "opensmt" && "$smtMode" == "proof" ]]; then
    smtSolverCmd="opensmt-p"
elif [[ "$smtSolver" == "cvc5-lfsc" && "$smtMode" == "proof" ]]; then
    smtSolverCmd="cvc5 --produce-proofs --proof-format=lfsc --proof-granularity=theory-rewrite"
elif [[ "$smtSolver" == "cvc5-alethe" && "$smtMode" == "proof" ]]; then
    smtSolverCmd="cvc5 --produce-proofs --proof-format=alethe --proof-granularity=theory-rewrite --flatten-ho-chains"
elif [[ "$smtSolver" = "verit" ]]; then
    smtSolverCmd="veriT -s"
elif [[ "$smtSolver" = "smtinterpol" ]]; then
    smtSolverCmd="smtinterpol-2.5-1259-gf8124b1f.jar"
    jvm="java -Xmx$jvmMemLimit -jar"
fi

cd ../witnesses_${chcSolver}_$target/$chcFileName
file=$chcFileName # done for historic reasons, awating refactoring
f=./$smtFileName # done for historic reasons, awating refactoring

if grep -Fqw "forall" $f || grep -Fqw "exists" $f; then
    if grep -Fqw "QF_LIA" $f; then
        sed -i '2d' $f # remove second line
        sed -i '3 i (set-logic LIA)' $f
    fi
fi

if [[ "$smtMode" == "proof" ]]; then
    sed -i '1s/^/(set-option :produce-proofs true)\n/' $f
    sed -i '$ d' $f # remove last line
    echo "(get-proof)" >> $f
    echo "(exit)" >> $f
fi

cd ../../result_${smtSolver}_${smtMode}_${target}_$chcSolver
mkdir ${file}_${f:2}
cd ${file}_${f:2}
mv ../../witnesses_${chcSolver}_$target/$file/$f ./

# --format "file runtime(sec) max_memory(Kbytes)"
# runtime is given as userTime+sysTime, it should be equal to the CPU time used by ulimit
# ulimit and jvm memory options conflict with one another
if [[ "$jvm" == "" ]]; then
    /usr/bin/time --output ../_run_smt_solver.stats --append --format "${file}_${f:2} %U+%S %M" sh -c "ulimit -Sv $memLimit; ulimit -St $timeLimit; ../../../solvers_smt/$smtSolverCmd ${f:2}" &> ${file}_${f:2}.out_smt_solver
    exit_status=$?
else
    /usr/bin/time --output ../_run_smt_solver.stats --append --format "${file}_${f:2} %U+%S %M" sh -c "ulimit -St $timeLimit; $jvm ../../../solvers_smt/$smtSolverCmd ${f:2}" &> ${file}_${f:2}.out_smt_solver
    exit_status=$?
fi

runtime=$(grep "${file}_${f:2}" ../_run_smt_solver.stats | awk '{print $2}') # gets the second string in _run_smt_solver.stats for file
memoryUse=$(grep "${file}_${f:2}" ../_run_smt_solver.stats | awk '{print $3}') # gets the third string in _run_smt_solver.stats for file

# remove error in output if SAT, since we always ask for a proof
sed -i '/Command get-proof called, but solver is not in UNSAT state/d' ${file}_${f:2}.out_smt_solver # opensmt
sed -i '/proof is not available/d' ${file}_${f:2}.out_smt_solver # z3
sed -i '/status is not unsat/d' ${file}_${f:2}.out_smt_solver # verit
sed -i '/Cannot get proof unless in unsat mode/d' ${file}_${f:2}.out_smt_solver # cvc5
sed -i '/Logical context not inconsistent/d' ${file}_${f:2}.out_smt_solver # smtinterpol

result="none"
if [[ "$exit_status" -eq 152 ]] || grep -Fqw "interrupted by timeout" ${file}_${f:2}.out_smt_solver || grep -Fqw "CPU time limit exceeded" ${file}_${f:2}.out_smt_solver; then # timeout
    echo "${file}_${f:2} $runtime $memoryUse" >> ../_timeout_smt_solver.stats
    result="timeout"
elif [[ "$exit_status" -eq 139 ]] || grep -Fqw "out of memory" ${file}_${f:2}.out_smt_solver; then # memout
    echo "${file}_${f:2} $runtime $memoryUse" >> ../_memout_smt_solver.stats
    result="memout"
elif grep -Fqw "error : Non linear expression" ${file}_${f:2}.out_smt_solver; then # unsupported expression 
    echo "${file}_${f:2} $runtime $memoryUse" >> ../_unsupported_smt_solver.stats
    result="error"
elif grep -Fqw "unknown logic LIA" ${file}_${f:2}.out_smt_solver; then # unsupported theory
    echo "${file}_${f:2} $runtime $memoryUse" >> ../_unsupported_smt_solver.stats
    result="error"
elif grep -Fqw "unimplemented attributed term" ${file}_${f:2}.out_smt_solver; then # unsupported theory
    echo "${file}_${f:2} $runtime $memoryUse" >> ../_unsupported_smt_solver.stats
    result="error"
elif grep -Fqw "Fatal failure" ${file}_${f:2}.out_smt_solver; then # error result
    echo "${file}_${f:2} $runtime $memoryUse" >> ../_problem_smt_solver.stats
    result="error"
elif grep -Pq '(?<!\.)error' ${file}_${f:2}.out_smt_solver; then # error result; we check if .error is not a substring
    echo "${file}_${f:2} $runtime $memoryUse" >> ../_problem_smt_solver.stats
    result="error"
elif $(grep -m2 ^ ${file}_${f:2}.out_smt_solver | grep -Fqw "unknown"); then # unknown result; we only check the first two lines to avoid miscategorizing
    echo "${file}_${f:2} $runtime $memoryUse" >> ../_unknown_smt_solver.stats
    result="unknown"
elif grep -Fqw "sat" ${file}_${f:2}.out_smt_solver; then # SAT result
    echo "${file}_${f:2} $runtime $memoryUse" >> ../_sat_smt_solver.stats
    result="sat"
elif grep -Fqw "unsat" ${file}_${f:2}.out_smt_solver; then # UNSAT result
    echo "${file}_${f:2} $runtime $memoryUse" >> ../_unsat_smt_solver.stats
    result="unsat"
else
    echo "${file}_${f:2} $runtime $memoryUse" >> ../_uncategorized_smt_solver.stats
    result="uncategorized"
fi

if [[ "$result" == "unsat" ]]; then # log proof size
    if [[ "$smtSolver" == "opensmt" && "$smtMode" == "proof" ]]; then
        proofStats=$(du -sb "proof") # "size folder" string
        proofStatsArr=(${proofStats}) # (size, folder) array
        proofSize=${proofStatsArr[0]} # size in bytes
        proofName="${file}_${f:2}.out_smt_solver"
        echo "$proofName unsat $proofSize" >> ../_proof-size_${smtSolver}_${smtMode}_${target}_$chcSolver.dataPoints
    elif [[ "$smtMode" == "proof" ]]; then
        proofStats=$(du -sb "${file}_${f:2}.out_smt_solver") # "size file" string
        proofStatsArr=(${proofStats}) # (size, file) array
        proofSize=${proofStatsArr[0]} # size in bytes
        proofName=${proofStatsArr[1]}
        echo "$proofName unsat $proofSize" >> ../_proof-size_${smtSolver}_${smtMode}_${target}_$chcSolver.dataPoints
    fi
fi

if [[ "$smtMode" == "proof" && "$result" == "unsat" ]]; then
    ../../../scripts/run_smt_checker.sh ${file} ${f:2} $target $smtSolver $chcSolver # run proof checker
fi

rm $f # comment out to see the .smt2 instances generated

cd ../../witnesses_${chcSolver}_$target/$file