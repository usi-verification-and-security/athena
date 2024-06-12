#!/bin/bash

timeLimit=1800    # 30 minutes (in seconds)
memLimit=10000000 # 10 GB (in Kbytes)
jvmMemLimit="10g" # 10 GB

chcFileName="$1" # .smt2 file
smtFileName="$2" # .smt2 file
target="$3"      # test, LIA-lin, LIA-nonlin, LIA-Arrays-lin, LIA-Arrays-nonlin
smtSolver="$4"   # cvc5-lfsc, cvc5-alethe, cvc5-aletheLF, opensmt, smtinterpol, verit, z3
chcSolver="$5"   # eldarica, golem, spacer

file="${chcFileName}_${smtFileName}"

if [[ "$#" -ne 5 ]]; then
  echo "Usage: $0 *.smt2 *.smt2 target smtSolver chcSolver"
  exit 1
fi

if [[ "$target" != "test" && "$target" != "LIA-lin" && "$target" != "LIA-nonlin" && "$target" != "LIA-Arrays-lin" && "$target" != "LIA-Arrays-nonlin" ]]; then
    echo "target invalid: use test, LIA-lin, LIA-nonlin, LIA-Arrays-lin, or LIA-Arrays-nonlin"
    exit 1
fi

if [[ "$smtSolver" != "cvc5-lfsc" && "$smtSolver" != "cvc5-alethe" && "$smtSolver" != "cvc5-aletheLF" && "$smtSolver" != "opensmt" && "$smtSolver" != "smtinterpol" && "$smtSolver" != "verit" && "$smtSolver" != "z3" ]]; then
    echo "smtSolver invalid: use cvc5-lfsc, cvc5-alethe, cvc5-aletheLF, opensmt, smtinterpol, verit, z3"
    exit 1
fi

if [[ "$chcSolver" != "eldarica" && "$chcSolver" != "golem" && "$chcSolver" != "spacer" ]]; then
    echo "chcSolver invalid: use eldarica, golem, or spacer"
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
elif [[ "$smtSolver" == "cvc5-aletheLF" ]]; then
    smtChecker="alfc"
elif [[ "$smtSolver" == "smtinterpol" ]]; then
    smtChecker="smtinterpol-checker"
fi

smtTheory="none" # for tswc
if [[ "$target" == "test" ]]; then
    smtTheory="QF_LIA"
elif [[ "$target" == "LIA-lin" || "$target" == "LIA-nonlin" ]]; then
    smtTheory="QF_LIA"
elif [[ "$target" == "LIA-Arrays-lin" || "$target" == "LIA-Arrays-nonlin" ]]; then
    smtTheory="unsupported"
    if [[ "$smtChecker" == "tswc" ]]; then # tswc does not support arrays
        echo "$target is not supported by $smtChecker, skipping $file"
        exit 0
    fi
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

            smtChecker="tswc.sh proof ../../../binaries/smt_checkers/tswc/modules $smtTheory"

            # --format "file runtime(sec) max_memory(Kbytes)"
            # runtime is given as userTime+sysTime, it should be equal to the CPU time used by ulimit
            /usr/bin/time --output ../_run_smt_checker.stats --append --format "$file %U+%S %M" sh -c "ulimit -Sv $memLimit; ulimit -St $timeLimit; ../../../binaries/smt_checkers/$smtChecker" &> $file.out_smt_checker
            exit_status=$?

            smtChecker="tswc"

            runtime=$(grep "$file" ../_run_smt_checker.stats | awk '{print $2}') # gets the second string in _run_smt_checker.stats for file
            memoryUse=$(grep "$file" ../_run_smt_checker.stats | awk '{print $3}') # gets the third string in _run_smt_checker.stats for file

            result="none"
            if [[ "$exit_status" -eq 152 ]] || grep -Fqw "timeout" $file.out_smt_checker || grep -Fqw "CPU time limit exceeded" $file.out_smt_checker; then # timeout
                echo "$file $runtime $memoryUse" >> ../_timeout_smt_checker.stats
                result="timeout"
            elif [[ "$exit_status" -eq 139 ]] || grep -Fqw "memout" $file.out_smt_checker || grep -Fqw "out of memory" $file.out_smt_checker; then # memout
                echo "$file $runtime $memoryUse" >> ../_memout_smt_checker.stats
                result="memout"
            elif grep -Fqw "verified" $file.out_smt_checker; then # verified
                echo "$file $runtime $memoryUse" >> ../_verified_smt_checker.stats
                result="verified"
            else
                echo "$file $runtime $memoryUse" >> ../_uncategorized_smt_checker.stats
                result="uncategorized"
            fi

            echo "$smtFileName $result" >> ../../witnesses_${chcSolver}_$target/$chcFileName/_results_smt_checker_${smtChecker}_smt_solver_${smtSolver}.stats

            rm -rf proof
            rm -rf ../../result_${smtSolver}_proof_${target}_$chcSolver/$file/proof # also removes the original
            rm -f ../../result_${smtSolver}_proof_${target}_$chcSolver/$file/proof.tar.bz2 # also removes the compresed version
        elif [[ "$smtChecker" == "lfsc" && "$smtSolver" == "cvc5-lfsc" ]]; then
            cd ../../result_${smtChecker}_${target}_${smtSolver}_${chcSolver}
            mkdir $file
            cd $file
            cp -r ../../result_${smtSolver}_proof_${target}_$chcSolver/$file/$file.out_smt_solver ./
            sed -i '0,/^unsat$/d' $file.out_smt_solver # removes all lines until and including the one with "unsat"

            sigDir=../../../binaries/smt_checkers/lfsc/signatures
            sig="$sigDir/core_defs.plf $sigDir/util_defs.plf $sigDir/theory_def.plf $sigDir/nary_programs.plf $sigDir/boolean_programs.plf $sigDir/boolean_rules.plf $sigDir/cnf_rules.plf $sigDir/equality_rules.plf $sigDir/arith_programs.plf $sigDir/arith_rules.plf $sigDir/strings_programs.plf $sigDir/strings_rules.plf $sigDir/quantifiers_rules.plf"
            smtChecker="lfscc $sig $file.out_smt_solver"

            # --format "file runtime(sec) max_memory(Kbytes)"
            # runtime is given as userTime+sysTime, it should be equal to the CPU time used by ulimit
            /usr/bin/time --output ../_run_smt_checker.stats --append --format "$file %U+%S %M" sh -c "ulimit -Sv $memLimit; ulimit -St $timeLimit; ../../../binaries/smt_checkers/$smtChecker" &> $file.out_smt_checker
            exit_status=$?

            smtChecker="lfsc"

            runtime=$(grep "$file" ../_run_smt_checker.stats | awk '{print $2}') # gets the second string in _run_smt_checker.stats for file
            memoryUse=$(grep "$file" ../_run_smt_checker.stats | awk '{print $3}') # gets the third string in _run_smt_checker.stats for file

            result="none"
            if [[ "$exit_status" -eq 152 ]] || grep -Fqw "timeout" $file.out_smt_checker || grep -Fqw "CPU time limit exceeded" $file.out_smt_checker; then # timeout
                echo "$file $runtime $memoryUse" >> ../_timeout_smt_checker.stats
                result="timeout"
            elif [[ "$exit_status" -eq 139 ]] || grep -Fqw "memout" $file.out_smt_checker || grep -Fqw "out of memory" $file.out_smt_checker; then # memout
                echo "$file $runtime $memoryUse" >> ../_memout_smt_checker.stats
                result="memout"
            elif grep -Fqw "Error:" $file.out_smt_checker; then # error
                echo "$file $runtime $memoryUse" >> ../_problem_smt_checker.stats
                result="error"
            elif grep -Fqw "success" $file.out_smt_checker; then # verified
                echo "$file $runtime $memoryUse" >> ../_verified_smt_checker.stats
                result="verified"
            else
                echo "$file $runtime $memoryUse" >> ../_uncategorized_smt_checker.stats
                result="uncategorized"
            fi

            echo "$smtFileName $result" >> "../../witnesses_${chcSolver}_$target/$chcFileName/_results_smt_checker_${smtChecker}_smt_solver_${smtSolver}.stats"

            rm -f $file.out_smt_solver
            rm -f ../../result_${smtSolver}_proof_${target}_$chcSolver/$file/$file.out_smt_solver # also removes the original
        elif [[ "$smtChecker" == "carcara" && "$smtSolver" == "cvc5-alethe" ]]; then
            cd ../../result_${smtChecker}_${target}_${smtSolver}_${chcSolver}
            mkdir $file
            cd $file
            cp -r ../../result_${smtSolver}_proof_${target}_$chcSolver/$file/$file.out_smt_solver ./
            sed -i '0,/^unsat$/d' $file.out_smt_solver # removes all lines until and including the one with "unsat"

            smtChecker="carcara check --ignore-unknown-rules --allow-int-real-subtyping --expand-let-bindings $file.out_smt_solver ../../result_${smtSolver}_proof_${target}_$chcSolver/$file/$smtFileName" # options allow for holey proofs to be checked

            # --format "file runtime(sec) max_memory(Kbytes)"
            # runtime is given as userTime+sysTime, it should be equal to the CPU time used by ulimit
            /usr/bin/time --output ../_run_smt_checker.stats --append --format "$file %U+%S %M" sh -c "ulimit -Sv $memLimit; ulimit -St $timeLimit; ../../../binaries/smt_checkers/$smtChecker" &> $file.out_smt_checker
            exit_status=$?

            smtChecker="carcara"

            runtime=$(grep "$file" ../_run_smt_checker.stats | awk '{print $2}') # gets the second string in _run_smt_checker.stats for file
            memoryUse=$(grep "$file" ../_run_smt_checker.stats | awk '{print $3}') # gets the third string in _run_smt_checker.stats for file

            result="none"
            if [[ "$exit_status" -eq 152 ]] || grep -Fqw "timeout" $file.out_smt_checker || grep -Fqw "CPU time limit exceeded" $file.out_smt_checker; then # timeout
                echo "$file $runtime $memoryUse" >> ../_timeout_smt_checker.stats
                result="timeout"
            elif [[ "$exit_status" -eq 139 ]] || grep -Fqw "memout" $file.out_smt_checker || grep -Fqw "out of memory" $file.out_smt_checker; then # memout
                echo "$file $runtime $memoryUse" >> ../_memout_smt_checker.stats
                result="memout"
            elif grep -Fqw "parser error" $file.out_smt_checker; then # error
                echo "$file $runtime $memoryUse" >> ../_problem_smt_checker.stats
                result="error"
            elif grep -Fqw "checking failed" $file.out_smt_checker; then # invalid proof
                echo "$file $runtime $memoryUse" >> ../_invalid_smt_checker.stats
                result="invalid"
            elif grep -Fqw "valid" $file.out_smt_checker; then # verified
                echo "$file $runtime $memoryUse" >> ../_verified_smt_checker.stats
                result="verified"
            elif grep -Fqw "holey" $file.out_smt_checker; then # verified with holes
                echo "$file $runtime $memoryUse" >> ../_verified_smt_checker.stats
                echo "$file $runtime $memoryUse" >> ../_holey_smt_checker.stats
                result="holey"
            else
                echo "$file $runtime $memoryUse" >> ../_uncategorized_smt_checker.stats
                result="uncategorized"
            fi

            echo "$smtFileName $result" >> ../../witnesses_${chcSolver}_$target/$chcFileName/_results_smt_checker_${smtChecker}_smt_solver_${smtSolver}.stats

            rm -f $file.out_smt_solver
            rm -f ../../result_${smtSolver}_proof_${target}_$chcSolver/$file/$file.out_smt_solver # also removes the original
        elif [[ "$smtChecker" == "alfc" && "$smtSolver" == "cvc5-aletheLF" ]]; then
            cd ../../result_${smtChecker}_${target}_${smtSolver}_${chcSolver}
            mkdir $file
            cd $file
            cp -r ../../result_${smtSolver}_proof_${target}_$chcSolver/$file/$file.out_smt_solver ./

            sed -i '0,/^unsat$/d' $file.out_smt_solver # removes all lines until and including the one with "unsat"
            sed -i '1s|^|(include "../../../binaries/smt_checkers/alf/cvc5/Cvc5.smt3")\n|' $file.out_smt_solver # alfc requires the include of "Cvc5.smt3" in the proof

            smtChecker="alfc $file.out_smt_solver"

            # --format "file runtime(sec) max_memory(Kbytes)"
            # runtime is given as userTime+sysTime, it should be equal to the CPU time used by ulimit
            /usr/bin/time --output ../_run_smt_checker.stats --append --format "$file %U+%S %M" sh -c "ulimit -Sv $memLimit; ulimit -St $timeLimit; ../../../binaries/smt_checkers/$smtChecker" &> $file.out_smt_checker
            exit_status=$?

            smtChecker="alfc"

            runtime=$(grep "$file" ../_run_smt_checker.stats | awk '{print $2}') # gets the second string in _run_smt_checker.stats for file
            memoryUse=$(grep "$file" ../_run_smt_checker.stats | awk '{print $3}') # gets the third string in _run_smt_checker.stats for file

            result="none"
            if [[ "$exit_status" -eq 152 ]] || grep -Fqw "timeout" $file.out_smt_checker || grep -Fqw "CPU time limit exceeded" $file.out_smt_checker; then # timeout
                echo "$file $runtime $memoryUse" >> ../_timeout_smt_checker.stats
                result="timeout"
            elif [[ "$exit_status" -eq 139 ]] || grep -Fqw "memout" $file.out_smt_checker || grep -Fqw "out of memory" $file.out_smt_checker; then # memout
                echo "$file $runtime $memoryUse" >> ../_memout_smt_checker.stats
                result="memout"
            elif grep -Fqw "Error:" $file.out_smt_checker; then # error
                echo "$file $runtime $memoryUse" >> ../_problem_smt_checker.stats
                result="error"
            elif grep -Fqw "success" $file.out_smt_checker; then # verified
                echo "$file $runtime $memoryUse" >> ../_verified_smt_checker.stats
                result="verified"
            else
                echo "$file $runtime $memoryUse" >> ../_uncategorized_smt_checker.stats
                result="uncategorized"
            fi

            echo "$smtFileName $result" >> ../../witnesses_${chcSolver}_$target/$chcFileName/_results_smt_checker_${smtChecker}_smt_solver_${smtSolver}.stats

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
            smtChecker="smtinterpol-2.5-1256-g55d6ba76.jar de.uni_freiburg.informatik.ultimate.smtinterpol.proof.checker.Main ../../result_${smtSolver}_proof_${target}_$chcSolver/$file/$smtFileName $file.out_smt_solver"

            # --format "file runtime(sec) max_memory(Kbytes)"
            # runtime is given as userTime+sysTime, it should be equal to the CPU time used by ulimit
            # jvm memory options are used instead of ulimit, they cannot be used together because they conflict with one another 
            /usr/bin/time --output ../_run_smt_checker.stats --append --format "$file %U+%S %M" sh -c "ulimit -St $timeLimit; $jvm ../../../binaries/smt_checkers/$smtChecker" &> $file.out_smt_checker
            exit_status=$?

            smtChecker="smtinterpol-checker"

            runtime=$(grep "$file" ../_run_smt_checker.stats | awk '{print $2}') # gets the second string in _run_smt_checker.stats for file
            memoryUse=$(grep "$file" ../_run_smt_checker.stats | awk '{print $3}') # gets the third string in _run_smt_checker.stats for file

            result="none"
            if [[ "$exit_status" -eq 152 ]] || grep -Fqw "timeout" $file.out_smt_checker || grep -Fqw "CPU time limit exceeded" $file.out_smt_checker; then # timeout
                echo "$file $runtime $memoryUse" >> ../_timeout_smt_checker.stats
                result="timeout"
            elif [[ "$exit_status" -eq 139 ]] || grep -Fqw "memout" $file.out_smt_checker || grep -Fqw "out of memory" $file.out_smt_checker; then # memout
                echo "$file $runtime $memoryUse" >> ../_memout_smt_checker.stats
                result="memout"
            elif $(grep -m2 ^ $file.out_smt_checker | grep -Fqw "unknown"); then # unknown result; we only check the first two lines to avoid miscategorizing
                echo "$file $runtime $memoryUse" >> ../_unknown_smt_checker.stats
                result="unknown"
            elif grep -Fqw "The proof did not yield a contradiction" $file.out_smt_checker; then # invalid proof
                echo "$file $runtime $memoryUse" >> ../_invalid_smt_checker.stats
                result="invalid"
            elif grep -Fqw "invalid" $file.out_smt_checker; then # invalid proof
                echo "$file $runtime $memoryUse" >> ../_invalid_smt_checker.stats
                result="invalid"
            elif grep -Fqw "valid" $file.out_smt_checker; then # verified
                echo "$file $runtime $memoryUse" >> ../_verified_smt_checker.stats
                result="verified"
            else
                echo "$file $runtime $memoryUse" >> ../_uncategorized_smt_checker.stats
                result="uncategorized"
            fi

            echo "$smtFileName $result" >> ../../witnesses_${chcSolver}_$target/$chcFileName/_results_smt_checker_${smtChecker}_smt_solver_${smtSolver}.stats

            rm -f $file.out_smt_solver
            rm -f ../../result_${smtSolver}_proof_${target}_$chcSolver/$file/$file.out_smt_solver # also removes the original
        fi
    fi
fi
