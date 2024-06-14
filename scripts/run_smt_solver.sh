#!/bin/bash

timeLimit=1800    # 30 minutes (in seconds)
memLimit=10000000 # 10 GB (in Kbytes)
jvmMemLimit="10g" # 10 GB

chcFileName="$1" # .smt2 file
smtFileName="$2" # .smt2 file
target="$3"      # test, LIA-lin, LIA-nonlin, LIA-Arrays-lin, LIA-Arrays-nonlin
smtSolver="$4"   # cvc5, cvc5-lfsc, cvc5-alethe, cvc5-aletheLF, opensmt, smtinterpol, verit, z3
smtMode="$5"     # proof, noProof
chcSolver="$6"   # eldarica, golem, spacer

if [[ "$#" -ne 6 ]]; then
  echo "Usage: $0 *.smt2 *.smt2 target smtSolver smtMode chcSolver"
  exit 1
fi

if [[ "$target" != "test" && "$target" != "LIA-lin" && "$target" != "LIA-nonlin" && "$target" != "LIA-Arrays-lin" && "$target" != "LIA-Arrays-nonlin" ]]; then
    echo "target invalid: use test, LIA-lin, LIA-nonlin, LIA-Arrays-lin, or LIA-Arrays-nonlin"
    exit 1
fi

if [[ "$smtSolver" != "cvc5" && "$smtSolver" != "cvc5-lfsc" && "$smtSolver" != "cvc5-alethe" && "$smtSolver" != "cvc5-aletheLF" && "$smtSolver" != "opensmt" && "$smtSolver" != "smtinterpol" && "$smtSolver" != "verit" && "$smtSolver" != "z3" ]]; then
    echo "smtSolver invalid: use cvc5, cvc5-lfsc, cvc5-alethe, cvc5-aletheLF, opensmt, smtinterpol, verit, or z3"
    exit 1
fi

if [[ "$smtMode" != "proof" && "$smtMode" != "noProof" ]]; then
    echo "smtMode invalid: use proof, or noProof"
    exit 1
fi

if [[ "$chcSolver" != "eldarica" && "$chcSolver" != "golem" && "$chcSolver" != "spacer" ]]; then
    echo "chcSolver invalid: use eldarica, golem, or spacer"
    exit 1
fi

#########################

cd "$(dirname "$0")" # script's folder
cd "../results/result_${smtSolver}_${smtMode}_${target}_$chcSolver"

echo "Running $smtSolver in $smtMode mode with $chcFileName ($smtFileName) from $chcSolver"

if [[ "$target" == "LIA-Arrays-lin" || "$target" == "LIA-Arrays-nonlin" ]]; then
    # not all smt solvers support arrays
    if [[ "$smtSolver" == "verit" ]]; then
        echo "$target is not supported by $smtSolver, skipping $chcFileName ($smtFileName)"
        exit 0
    fi
    # some smt solvers support arrays but do not produce proofs for them
    if [[ "$smtMode" == "proof" ]]; then
        if [[ "$smtSolver" == "cvc5-alethe" || "$smtSolver" == "opensmt" ]]; then
            echo "$target is not supported by $smtSolver, skipping $chcFileName ($smtFileName)"
            exit 0
        fi
    fi
fi

smtSolverCmd=$smtSolver
jvm=""
if [[ "$smtSolver" == "opensmt" && "$smtMode" == "proof" ]]; then
    smtSolverCmd="opensmt-p"
elif [[ "$smtSolver" == "cvc5-lfsc" && "$smtMode" == "proof" ]]; then
    smtSolverCmd="cvc5 --proof-format=lfsc --proof-granularity=theory-rewrite"
elif [[ "$smtSolver" == "cvc5-alethe" && "$smtMode" == "proof" ]]; then
    smtSolverCmd="cvc5 --proof-format=alethe --proof-granularity=theory-rewrite --flatten-ho-chains"
elif [[ "$smtSolver" == "cvc5-aletheLF" && "$smtMode" == "proof" ]]; then
    smtSolverCmd="cvc5 --proof-format=alf --proof-granularity=theory-rewrite"
elif [[ "$smtSolver" = "verit" ]]; then
    smtSolverCmd="veriT -s"
elif [[ "$smtSolver" = "smtinterpol" ]]; then
    smtSolverCmd="smtinterpol-2.5-1256-g55d6ba76.jar"
    jvm="java -Xmx$jvmMemLimit -jar"
fi

cd ../witnesses_${chcSolver}_$target/$chcFileName
file=$chcFileName # done for historic reasons, awaiting refactoring
f=./$smtFileName # done for historic reasons, awaiting refactoring

if [[ "$smtMode" == "proof" ]]; then
    sed -i '1s/^/(set-option :produce-proofs true)\n/' $f
    sed -i '$ d' $f # remove last line
    echo "(get-proof)" >> $f
    echo "(exit)" >> $f
fi

# remove array logic for z3, see https://github.com/Z3Prover/z3/issues/6545
if [[ "$smtSolver" == "z3" ]]; then
    sed -i '/(set-logic ALIA)/d' $f
    sed -i '/(set-logic QF_ALIA)/d' $f
fi

cd ../../result_${smtSolver}_${smtMode}_${target}_$chcSolver
mkdir ${file}_${f:2}
cd ${file}_${f:2}
mv ../../witnesses_${chcSolver}_$target/$file/$f ./

# --format "file runtime(sec) max_memory(Kbytes)"
# runtime is given as userTime+sysTime, it should be equal to the CPU time used by ulimit
# ulimit and jvm memory options conflict with one another
if [[ "$jvm" == "" ]]; then
    /usr/bin/time --output ../_run_smt_solver.stats --append --format "${file}_${f:2} %U+%S %M" sh -c "ulimit -Sv $memLimit; ulimit -St $timeLimit; ../../../binaries/smt_solvers/$smtSolverCmd ${f:2}" &> ${file}_${f:2}.out_smt_solver
    exit_status=$?
else
    /usr/bin/time --output ../_run_smt_solver.stats --append --format "${file}_${f:2} %U+%S %M" sh -c "ulimit -St $timeLimit; $jvm ../../../binaries/smt_solvers/$smtSolverCmd ${f:2}" &> ${file}_${f:2}.out_smt_solver
    exit_status=$?
fi

runtime=$(grep "${file}_${f:2}" ../_run_smt_solver.stats | awk '{print $2}') # gets the second string in _run_smt_solver.stats for file
memoryUse=$(grep "${file}_${f:2}" ../_run_smt_solver.stats | awk '{print $3}') # gets the third string in _run_smt_solver.stats for file

# remove error in output if SAT, since we always ask for a proof
sed -i '/Cannot get proof unless in unsat mode/d' ${file}_${f:2}.out_smt_solver # cvc5
sed -i '/Command get-proof called, but solver is not in UNSAT state/d' ${file}_${f:2}.out_smt_solver # opensmt
sed -i '/Logical context not inconsistent/d' ${file}_${f:2}.out_smt_solver # smtinterpol
sed -i '/status is not unsat/d' ${file}_${f:2}.out_smt_solver # verit
sed -i '/proof is not available/d' ${file}_${f:2}.out_smt_solver # z3

result="none"
if [[ "$exit_status" -eq 152 ]] || grep -Fqw "interrupted by timeout" ${file}_${f:2}.out_smt_solver || grep -Fqw "CPU time limit exceeded" ${file}_${f:2}.out_smt_solver || grep -Fqw "Killed" ${file}_${f:2}.out_smt_solver; then # timeout
    echo "${file}_${f:2} $runtime $memoryUse" >> ../_timeout_smt_solver.stats
    result="timeout"
elif [[ "$exit_status" -eq 139 ]] || grep -Fqw "out of memory" ${file}_${f:2}.out_smt_solver || grep -Fqw "Invalid memory reference" ${file}_${f:2}.out_smt_solver || grep -Fqw "OutOfMemoryError" ${file}_${f:2}.out_smt_solver || grep -Fqw "StackOverflowError" ${file}_${f:2}.out_smt_solver || grep -Fqw "std::bad_alloc" ${file}_${f:2}.out_smt_solver; then # memout
    echo "${file}_${f:2} $runtime $memoryUse" >> ../_memout_smt_solver.stats
    result="memout"
elif grep -Fqw "error : Non linear expression" ${file}_${f:2}.out_smt_solver; then # unsupported expression 
    echo "${file}_${f:2} $runtime $memoryUse" >> ../_unsupported_smt_solver.stats
    result="unsupported"
elif grep -Fqw "unknown logic LIA" ${file}_${f:2}.out_smt_solver; then # unsupported theory
    echo "${file}_${f:2} $runtime $memoryUse" >> ../_unsupported_smt_solver.stats
    result="unsupported"
elif grep -Fqw "unknown logic ALIA" ${file}_${f:2}.out_smt_solver; then # unsupported theory
    echo "${file}_${f:2} $runtime $memoryUse" >> ../_unsupported_smt_solver.stats
    result="unsupported"
elif grep -Fqw "unimplemented attributed term" ${file}_${f:2}.out_smt_solver; then # unsupported theory
    echo "${file}_${f:2} $runtime $memoryUse" >> ../_unsupported_smt_solver.stats
    result="unsupported"
elif grep -Fqw "Fatal failure" ${file}_${f:2}.out_smt_solver; then # error result
    echo "${file}_${f:2} $runtime $memoryUse" >> ../_problem_smt_solver.stats
    result="error"
elif grep -Pq '(?<!\.|\$)error' ${file}_${f:2}.out_smt_solver; then # error result; we check if .error and $error are not a substring
    echo "${file}_${f:2} $runtime $memoryUse" >> ../_problem_smt_solver.stats
    result="error"
elif grep -Pq '(?<!\.|\$)unknown' ${file}_${f:2}.out_smt_solver; then # unknown result; we check if .unknown and $unknown are not a substring
    echo "${file}_${f:2} $runtime $memoryUse" >> ../_unknown_smt_solver.stats
    result="unknown"
elif [[ "$smtSolver" == "smtinterpol" ]] && grep -Fqw "unknown" ${file}_${f:2}.out_smt_solver; then # unknown result; only for smtinterpol
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

echo "$smtFileName $result" >> ../../witnesses_${chcSolver}_$target/$chcFileName/_results_smt_solver_${smtSolver}_${smtMode}.stats

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

rm $f # comment out to keep the .smt2 instances generated
