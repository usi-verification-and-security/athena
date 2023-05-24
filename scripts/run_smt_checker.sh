#!/bin/bash

timeLimit=60     # 1 minute (in seconds)
memLimit=5000000 # 5 GB (in Kbytes)
jvmMemLimit="5g" # 5 GB

chcFileName="$1" # .smt2 file
smtFileName="$2" # .smt2 file
target="$3"      # test, LIA-lin, LIA-nonlin
smtSolver="$4"   # opensmt, z3, verit, cvc5-lfsc, cvc5-alethe, smtinterpol
chcSolver="$5"   # golem, eldarica, spacer

file="${chcFileName}_${smtFileName}"

if [[ "$#" -ne 5 ]]; then
  echo "Usage: $0 *.smt2 *.smt2 target smtSolver chcSolver"
  exit 1
fi

if [[ "$target" != "test" && "$target" != "LIA-lin" && "$target" != "LIA-nonlin" ]]; then
    echo "target invalid: use test, LIA-lin, or LIA-nonlin"
    exit 1
fi

if [[ "$smtSolver" != "opensmt" && "$smtSolver" != "z3" && "$smtSolver" != "verit" && "$smtSolver" != "cvc5-lfsc" && "$smtSolver" != "cvc5-alethe" && "$smtSolver" != "smtinterpol" ]]; then
    echo "smtSolver invalid: use opensmt, z3, verit, cvc5-lfsc, cvc5-alethe, or smtinterpol"
    exit 1
fi

if [[ "$chcSolver" != "golem" && "$chcSolver" != "eldarica" && "$chcSolver" != "spacer" ]]; then
    echo "chcSolver invalid: use golem, eldarica, or spacer"
    exit 1
fi

#########################

cd "$(dirname "$0")" # script's folder
cd ../results/result_${smtSolver}_proof_${target}_$chcSolver/$file

smtChecker="none"
if [[ "$smtSolver" == "opensmt" ]]; then
    smtChecker="tswc"
elif [[ "$smtSolver" == "cvc5-lfsc" ]]; then
    smtChecker="lfsc"
elif [[ "$smtSolver" == "cvc5-alethe" ]]; then
    smtChecker="carcara"
elif [[ "$smtSolver" == "smtinterpol" ]]; then
    smtChecker="smtinterpol-checker"
fi

smtTheory="none"
if [[ "$target" == "test" ]]; then
    smtTheory="QF_LIA"
elif [[ "$target" == "LIA-lin" || "$target" == "LIA-nonlin" ]]; then
    smtTheory="QF_LIA"
fi

if grep -Fqw "unsat" $file.out_smt_solver; then # UNSAT result
    if [[ "$smtChecker" == "none" ]]; then
        rm -f ../../result_${smtSolver}_proof_${target}_$chcSolver/$file/$file.out_smt_solver # removes the proof
    else
        echo "Running $smtChecker with $file from $smtSolver and $chcSolver"

        if [[ "$smtChecker" == "tswc" && "$smtSolver" == "opensmt" ]]; then
            cd ../../result_${smtChecker}_${target}_${smtSolver}_${chcSolver}
            mkdir $file
            cd $file
            cp -r ../../result_${smtSolver}_proof_${target}_$chcSolver/$file/proof ./

            smtChecker="tswc.sh proof ../../../checkers_smt/modules $smtTheory"

            # --format "file runtime(sec) max_memory(Kbytes)"
            # runtime is given as userTime+sysTime, it should be equal to the CPU time used by ulimit
            /usr/bin/time --output ../_run_smt_checker.stats --append --format "$file %U+%S %M" sh -c "ulimit -Sv $memLimit; ulimit -St $timeLimit; ../../../checkers_smt/$smtChecker" &> $file.out_smt_checker
            exit_status=$?

            runtime=$(grep "$file" ../_run_smt_checker.stats | awk '{print $2}') # gets the second string in _run_smt_checker.stats for file
            memoryUse=$(grep "$file" ../_run_smt_checker.stats | awk '{print $3}') # gets the third string in _run_smt_checker.stats for file

            if [[ "$exit_status" -eq 152 ]] || grep -Fqw "timeout" $file.out_smt_checker || grep -Fqw "CPU time limit exceeded" $file.out_smt_checker; then # timeout
                echo "$file $runtime $memoryUse" >> ../_timeout_smt_checker.stats
            elif [[ "$exit_status" -eq 139 ]] || grep -Fqw "memout" $file.out_smt_checker || grep -Fqw "out of memory" $file.out_smt_checker; then # memout
                echo "$file $runtime $memoryUse" >> ../_memout_smt_checker.stats
            elif grep -Fqw "verified" $file.out_smt_checker; then # verified
                echo "$file $runtime $memoryUse" >> ../_verified_smt_checker.stats
            else
                echo "$file $runtime $memoryUse" >> ../_uncategorized_smt_checker.stats
            fi

            rm -rf proof
            rm -rf ../../result_${smtSolver}_proof_${target}_$chcSolver/$file/proof # also removes the original
            rm -f ../../result_${smtSolver}_proof_${target}_$chcSolver/$file/proof.tar.bz2 # also removes the compresed version
        elif [[ "$smtChecker" == "lfsc" && "$smtSolver" == "cvc5-lfsc" ]]; then
            cd ../../result_${smtChecker}_${target}_${smtSolver}_${chcSolver}
            mkdir $file
            cd $file
            cp -r ../../result_${smtSolver}_proof_${target}_$chcSolver/$file/$file.out_smt_solver ./
            sed -i '0,/^unsat$/d' $file.out_smt_solver # removes all lines until and including the one with "unsat"

            sigDir=../../../checkers_smt/signatures
            sig="$sigDir/core_defs.plf $sigDir/util_defs.plf $sigDir/theory_def.plf $sigDir/nary_programs.plf $sigDir/boolean_programs.plf $sigDir/boolean_rules.plf $sigDir/cnf_rules.plf $sigDir/equality_rules.plf $sigDir/arith_programs.plf $sigDir/arith_rules.plf $sigDir/strings_programs.plf $sigDir/strings_rules.plf $sigDir/quantifiers_rules.plf"
            smtChecker="lfscc $sig $file.out_smt_solver"

            # --format "file runtime(sec) max_memory(Kbytes)"
            # runtime is given as userTime+sysTime, it should be equal to the CPU time used by ulimit
            /usr/bin/time --output ../_run_smt_checker.stats --append --format "$file %U+%S %M" sh -c "ulimit -Sv $memLimit; ulimit -St $timeLimit; ../../../checkers_smt/$smtChecker" &> $file.out_smt_checker
            exit_status=$?

            runtime=$(grep "$file" ../_run_smt_checker.stats | awk '{print $2}') # gets the second string in _run_smt_checker.stats for file
            memoryUse=$(grep "$file" ../_run_smt_checker.stats | awk '{print $3}') # gets the third string in _run_smt_checker.stats for file

            if [[ "$exit_status" -eq 152 ]] || grep -Fqw "timeout" $file.out_smt_checker || grep -Fqw "CPU time limit exceeded" $file.out_smt_checker; then # timeout
                echo "$file $runtime $memoryUse" >> ../_timeout_smt_checker.stats
            elif [[ "$exit_status" -eq 139 ]] || grep -Fqw "memout" $file.out_smt_checker || grep -Fqw "out of memory" $file.out_smt_checker; then # memout
                echo "$file $runtime $memoryUse" >> ../_memout_smt_checker.stats
            elif grep -Fqw "Error:" $file.out_smt_checker; then # error
                echo "$file $runtime $memoryUse" >> ../_problem_smt_checker.stats
            elif grep -Fqw "success" $file.out_smt_checker; then # verified
                echo "$file $runtime $memoryUse" >> ../_verified_smt_checker.stats
            else
                echo "$file $runtime $memoryUse" >> ../_uncategorized_smt_checker.stats
            fi

            rm -f $file.out_smt_solver
            rm -f ../../result_${smtSolver}_proof_${target}_$chcSolver/$file/$file.out_smt_solver # also removes the original
        elif [[ "$smtChecker" == "carcara" && "$smtSolver" == "cvc5-alethe" ]]; then
            cd ../../result_${smtChecker}_${target}_${smtSolver}_${chcSolver}
            mkdir $file
            cd $file
            cp -r ../../result_${smtSolver}_proof_${target}_$chcSolver/$file/$file.out_smt_solver ./
            sed -i '0,/^unsat$/d' $file.out_smt_solver # removes all lines until and including the one with "unsat"

            smtChecker="carcara/target/release/carcara check --skip-unknown-rules --allow-int-real-subtyping --expand-let-bindings $file.out_smt_solver ../../result_${smtSolver}_proof_${target}_$chcSolver/$file/$smtFileName" # options allow for holey proofs to be checked

            # --format "file runtime(sec) max_memory(Kbytes)"
            # runtime is given as userTime+sysTime, it should be equal to the CPU time used by ulimit
            /usr/bin/time --output ../_run_smt_checker.stats --append --format "$file %U+%S %M" sh -c "ulimit -Sv $memLimit; ulimit -St $timeLimit; ../../../checkers_smt/$smtChecker" &> $file.out_smt_checker
            exit_status=$?

            runtime=$(grep "$file" ../_run_smt_checker.stats | awk '{print $2}') # gets the second string in _run_smt_checker.stats for file
            memoryUse=$(grep "$file" ../_run_smt_checker.stats | awk '{print $3}') # gets the third string in _run_smt_checker.stats for file

            if [[ "$exit_status" -eq 152 ]] || grep -Fqw "timeout" $file.out_smt_checker || grep -Fqw "CPU time limit exceeded" $file.out_smt_checker; then # timeout
                echo "$file $runtime $memoryUse" >> ../_timeout_smt_checker.stats
            elif [[ "$exit_status" -eq 139 ]] || grep -Fqw "memout" $file.out_smt_checker || grep -Fqw "out of memory" $file.out_smt_checker; then # memout
                echo "$file $runtime $memoryUse" >> ../_memout_smt_checker.stats
            elif grep -Fqw "parser error" $file.out_smt_checker; then # error
                echo "$file $runtime $memoryUse" >> ../_problem_smt_checker.stats
            elif grep -Fqw "checking failed" $file.out_smt_checker; then # invalid proof
                echo "$file $runtime $memoryUse" >> ../_invalid_smt_checker.stats
            elif grep -Fqw "valid" $file.out_smt_checker; then # verified
                echo "$file $runtime $memoryUse" >> ../_verified_smt_checker.stats
            elif grep -Fqw "holey" $file.out_smt_checker; then # verified with holes
                echo "$file $runtime $memoryUse" >> ../_verified_smt_checker.stats
                echo "$file $runtime $memoryUse" >> ../_holey_smt_checker.stats
            else
                echo "$file $runtime $memoryUse" >> ../_uncategorized_smt_checker.stats
            fi

            rm -f $file.out_smt_solver
            rm -f ../../result_${smtSolver}_proof_${target}_$chcSolver/$file/$file.out_smt_solver # also removes the original
        elif [[ "$smtChecker" == "smtinterpol-checker" && "$smtSolver" == "smtinterpol" ]]; then
            cd ../../result_${smtChecker}_${target}_${smtSolver}_${chcSolver}
            mkdir $file
            cd $file
            cp -r ../../result_${smtSolver}_proof_${target}_$chcSolver/$file/$file.out_smt_solver ./
            sed -i '0,/^unsat$/d' $file.out_smt_solver # removes all lines until and including the one with "unsat"
            sed -i '1s/^/unsat\n/' $file.out_smt_solver # smtinterpol-checker requires "unsat" in the proof

            jvm="java -Xmx$jvmMemLimit -cp"
            smtChecker="smtinterpol-2.5-1259-gf8124b1f.jar de.uni_freiburg.informatik.ultimate.smtinterpol.proof.checker.Main ../../result_${smtSolver}_proof_${target}_$chcSolver/$file/$smtFileName $file.out_smt_solver"

            # --format "file runtime(sec) max_memory(Kbytes)"
            # runtime is given as userTime+sysTime, it should be equal to the CPU time used by ulimit
            # jvm memory options are used instead of ulimit, they cannot be used together because they conflict with one another 
            /usr/bin/time --output ../_run_smt_checker.stats --append --format "$file %U+%S %M" sh -c "ulimit -St $timeLimit; $jvm ../../../checkers_smt/$smtChecker" &> $file.out_smt_checker
            exit_status=$?

            runtime=$(grep "$file" ../_run_smt_checker.stats | awk '{print $2}') # gets the second string in _run_smt_checker.stats for file
            memoryUse=$(grep "$file" ../_run_smt_checker.stats | awk '{print $3}') # gets the third string in _run_smt_checker.stats for file

            if [[ "$exit_status" -eq 152 ]] || grep -Fqw "timeout" $file.out_smt_checker || grep -Fqw "CPU time limit exceeded" $file.out_smt_checker; then # timeout
                echo "$file $runtime $memoryUse" >> ../_timeout_smt_checker.stats
            elif [[ "$exit_status" -eq 139 ]] || grep -Fqw "memout" $file.out_smt_checker || grep -Fqw "out of memory" $file.out_smt_checker; then # memout
                echo "$file $runtime $memoryUse" >> ../_memout_smt_checker.stats
            elif $(grep -m2 ^ $file.out_smt_checker | grep -Fqw "unknown"); then # unknown result; we only check the first two lines to avoid miscategorizing
                echo "$file $runtime $memoryUse" >> ../_unknown_smt_checker.stats
            elif grep -Fqw "The proof did not yield a contradiction" $file.out_smt_checker; then # invalid proof
                echo "$file $runtime $memoryUse" >> ../_invalid_smt_checker.stats
            elif grep -Fqw "invalid" $file.out_smt_checker; then # invalid proof
                echo "$file $runtime $memoryUse" >> ../_invalid_smt_checker.stats
            elif grep -Fqw "valid" $file.out_smt_checker; then # verified
                echo "$file $runtime $memoryUse" >> ../_verified_smt_checker.stats
            else
                echo "$file $runtime $memoryUse" >> ../_uncategorized_smt_checker.stats
            fi

            rm -f $file.out_smt_solver
            rm -f ../../result_${smtSolver}_proof_${target}_$chcSolver/$file/$file.out_smt_solver # also removes the original
        fi
    fi
fi