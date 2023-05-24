#!/bin/bash

chcSolver="$1" # all, none, golem, eldarica, spacer
smtSolver="$2" # all, none, opensmt, z3, verit, cvc5, smtinterpol
smtMode="$3"   # all, proof, noProof
target="$4"    # all, test, LIA-lin, LIA-nonlin
threads="$5"   # e.g. 16

if [[ "$#" -ne 5 ]]; then
  echo "Usage: $0 chcSolver smtSolver smtMode target threads"
  exit 1
fi

if [[ "$chcSolver" != "all" && "$chcSolver" != "none" && "$chcSolver" != "golem" && "$chcSolver" != "eldarica" && "$chcSolver" != "spacer" ]]; then
    echo "chcSolver invalid: use all, none, golem, eldarica, or spacer"
    exit 1
fi

if [[ "$smtSolver" != "all" && "$smtSolver" != "none" && "$smtSolver" != "opensmt" && "$smtSolver" != "z3" && "$smtSolver" != "verit" && "$smtSolver" != "cvc5" && "$smtSolver" != "smtinterpol" ]]; then
    echo "Tool invalid: use all, none, opensmt, z3, verit, cvc5, or smtinterpol"
    exit 1
fi

if [[ "$smtMode" != "all" && "$smtMode" != "proof" && "$smtMode" != "noProof" ]]; then
    echo "smtMode invalid: use all, proof, or noProof"
    exit 1
fi

if [[ "$target" != "all" && "$target" != "test" && "$target" != "LIA-lin" && "$target" != "LIA-nonlin" ]]; then
    echo "target invalid: use all, test, LIA-lin, or LIA-nonlin"
    exit 1
fi

if [[ "$threads" -eq 0 ]]; then
    echo "Number of threads invalid"
    exit 1
fi

#########################

if !(test -d "../results"); then mkdir "../results"; fi

./evaluate_chc_solver.sh $chcSolver $target $threads
./evaluate_smt_solver.sh $smtSolver $smtMode $target $threads