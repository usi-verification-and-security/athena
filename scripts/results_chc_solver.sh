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
cd ../results/witnesses_${chcSolver}_$target

#########################

function count_entries () {
    # $1 file name
    # $2 counter variable name
    # $3 string to match

    if test -f "$1"; then
        if [[ $(wc -w < "$1") -gt 0 ]]; then
            eval "$2=$(grep -o $3 $1 | wc -l)"
        fi
    fi
}

function call_count_entries () {
    # $1 file name

    count_valid=0
    count_holey=0
    count_invalid=0
    count_unknown=0
    count_error=0
    count_unsupported=0
    count_memout=0
    count_timeout=0
    count_uncategorized=0

    count_entries $1 "count_valid"         "valid"
    count_entries $1 "count_holey"         "holey" # for proofs that are valid but have holes
    count_entries $1 "count_invalid"       "invalid"
    count_entries $1 "count_unknown"       "unknown"
    count_entries $1 "count_error"         "error"
    count_entries $1 "count_unsupported"   "unsupported"
    count_entries $1 "count_timeout"       "timeout"
    count_entries $1 "count_memout"        "memout"    
    count_entries $1 "count_uncategorized" "uncategorized"

    count_valid=$((count_valid+count_holey))

    total=$((count_valid + count_invalid + count_unknown + count_error + count_unsupported + count_timeout + count_memout + count_uncategorized))

    echo "********** Results for $chcSolver with $target: $1 **********"
    echo "Benchmarks analysed: $total"
    echo "valid: $count_valid ($count_holey holey)"
    echo "invalid: $count_invalid"
    echo "unknown: $count_unknown"
    echo "unsupported: $count_unsupported"
    echo "timeout: $count_timeout"
    echo "memout: $count_memout"
    echo "error: $count_error"    
    echo "uncategorized: $count_uncategorized"
}

#########################

call_count_entries "_results_smt_solver_cvc5_noProof.stats"
call_count_entries "_results_smt_solver_opensmt_noProof.stats"
call_count_entries "_results_smt_solver_smtinterpol_noProof.stats"
call_count_entries "_results_smt_solver_verit_noProof.stats"
call_count_entries "_results_smt_solver_z3_noProof.stats"

call_count_entries "_results_smt_solver_cvc5-aletheLF_proof.stats"
call_count_entries "_results_smt_checker_alfc_smt_solver_cvc5-aletheLF.stats"

call_count_entries "_results_smt_solver_cvc5-alethe_proof.stats"
call_count_entries "_results_smt_checker_carcara_smt_solver_cvc5-alethe.stats"

call_count_entries "_results_smt_solver_cvc5-lfsc_proof.stats"
call_count_entries "_results_smt_checker_lfsc_smt_solver_cvc5-lfsc.stats"

call_count_entries "_results_smt_solver_opensmt_proof.stats"
call_count_entries "_results_smt_checker_tswc_smt_solver_opensmt.stats"

call_count_entries "_results_smt_solver_smtinterpol_proof.stats"
call_count_entries "_results_smt_checker_smtinterpol-checker_smt_solver_smtinterpol.stats"

#call_count_entries "_results_smt_solver_verit_proof.stats"
# verit cannot produce proofs for the benchmarks at present

#call_count_entries "_results_smt_solver_z3_proof.stats"
# z3 has not independent proof checker at present
