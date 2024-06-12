#!/bin/bash

chcSolver="$1" # all, none, eldarica, golem, spacer
smtSolver="$2" # all, none, cvc5, opensmt, smtinterpol, verit, z3
smtMode="$3"   # all, proof, noProof
target="$4"    # all, test, LIA-lin, LIA-nonlin, LIA-Arrays-lin, LIA-Arrays-nonlin
threads="$5"   # e.g. 16

if [[ "$#" -ne 5 ]]; then
  echo "Usage: $0 chcSolver smtSolver smtMode target threads"
  exit 1
fi

if [[ "$chcSolver" != "all" && "$chcSolver" != "none" && "$chcSolver" != "eldarica" && "$chcSolver" != "golem" && "$chcSolver" != "spacer" ]]; then
    echo "chcSolver invalid: use all, none, eldarica, golem, or spacer"
    exit 1
fi

if [[ "$smtSolver" != "all" && "$smtSolver" != "none" && "$smtSolver" != "cvc5" && "$smtSolver" != "opensmt" && "$smtSolver" != "smtinterpol" && "$smtSolver" != "verit" && "$smtSolver" != "z3" ]]; then
    echo "smtSolver invalid: use all, none, cvc5, opensmt, smtinterpol, verit, or z3"
    exit 1
fi

if [[ "$smtMode" != "all" && "$smtMode" != "proof" && "$smtMode" != "noProof" ]]; then
    echo "smtMode invalid: use all, proof, or noProof"
    exit 1
fi

if [[ "$target" != "all" && "$target" != "test" && "$target" != "LIA-lin" && "$target" != "LIA-nonlin" && "$target" != "LIA-Arrays-lin" && "$target" != "LIA-Arrays-nonlin" ]]; then
    echo "target invalid: use all, test, LIA-lin, LIA-nonlin, LIA-Arrays-lin, or LIA-Arrays-nonlin"
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
