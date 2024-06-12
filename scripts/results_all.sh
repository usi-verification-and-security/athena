#!/bin/bash

specificTarget=$1 # e.g., test

#########################

function chc_solver_results_call () {
    # $1 chcSolver
    # $2 target

    ./results_chc_solver.sh $1 $2
}

function chc_solver_results_by_target () {
    # $1 chcSolver

    if [[ "$specificTarget" != "" ]]; then
        chc_solver_results_call $1 $specificTarget
    else
        chc_solver_results_call $1 "LIA-lin"
        chc_solver_results_call $1 "LIA-nonlin"
        chc_solver_results_call $1 "LIA-Arrays-lin"
        chc_solver_results_call $1 "LIA-Arrays-nonlin"
    fi
}

function chc_solver_results_by_chc_solver () {
    chc_solver_results_by_target "eldarica"
    chc_solver_results_by_target "golem"
    chc_solver_results_by_target "spacer"
}

function chc_solver_results () {
    chc_solver_results_by_chc_solver
}

#########################

chc_solver_results
