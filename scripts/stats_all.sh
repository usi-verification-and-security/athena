#!/bin/bash

specificTarget=$1 # e.g., test

#########################

function chc_solver_stats_call () {
    # $1 chcSolver
    # $2 target

    ./stats_chc_solver.sh $1 $2
}

function chc_solver_stats_by_target () {
    # $1 chcSolver

    if [[ "$specificTarget" != "" ]]; then
        chc_solver_stats_call $1 $specificTarget
    else
        chc_solver_stats_call $1 "LIA-lin"
        chc_solver_stats_call $1 "LIA-nonlin"
    fi
}

function chc_solver_stats_by_chc_solver () {
    chc_solver_stats_by_target "golem"
    chc_solver_stats_by_target "eldarica"
    chc_solver_stats_by_target "spacer"
}

function chc_solver_stats () {
    chc_solver_stats_by_chc_solver
}

#########################

function smt_solver_stats_call () {
    # $1 smtMode
    # $2 smtSolver
    # $3 chcSolver
    # $4 target

    ./stats_smt_solver.sh $2 $1 $4 $3
}

function smt_solver_stats_by_target () {
    # $1 smtMode
    # $2 smtSolver
    # $3 chcSolver

    if [[ "$specificTarget" != "" ]]; then
        smt_solver_stats_call $1 $2 $3 $specificTarget
    else
        smt_solver_stats_call $1 $2 $3 "LIA-lin"
        smt_solver_stats_call $1 $2 $3 "LIA-nonlin"
    fi
}

function smt_solver_stats_by_chc_solver () {
    # $1 smtMode
    # $2 smtSolver

    smt_solver_stats_by_target $1 $2 "golem"
    smt_solver_stats_by_target $1 $2 "eldarica"
    smt_solver_stats_by_target $1 $2 "spacer"
}

function smt_solver_stats_by_smt_solver () {
    # $1 smtMode

    smt_solver_stats_by_chc_solver $1 "opensmt"
    smt_solver_stats_by_chc_solver $1 "z3"
    smt_solver_stats_by_chc_solver $1 "verit"
    smt_solver_stats_by_chc_solver $1 "smtinterpol"

    if [[ "$1" == "proof" ]]; then
        smt_solver_stats_by_chc_solver $1 "cvc5-lfsc"
        smt_solver_stats_by_chc_solver $1 "cvc5-alethe"
    elif [[ "$1" == "noProof" ]]; then
        smt_solver_stats_by_chc_solver $1 "cvc5"
    fi
}

function smt_solver_stats_by_smt_mode () {
    smt_solver_stats_by_smt_solver "proof"
    smt_solver_stats_by_smt_solver "noProof"
}

function smt_solver_stats () {
    smt_solver_stats_by_smt_mode
}

#########################

function smt_checker_stats_call () {
    # $1 smtChecker
    # $2 smtSolver
    # $3 chcSolver
    # $4 target

    ./stats_smt_checker.sh $1 $2 $4 $3
}

function smt_checker_stats_by_target () {
    # $1 smtChecker
    # $2 smtSolver
    # $3 chcSolver

    if [[ "$specificTarget" != "" ]]; then
        smt_checker_stats_call $1 $2 $3 $specificTarget
    else
        smt_checker_stats_call $1 $2 $3 "LIA-lin"
        smt_checker_stats_call $1 $2 $3 "LIA-nonlin"
    fi
}

function smt_checker_stats_by_chc_solver () {
    # $1 smtChecker
    # $2 smtSolver

    smt_checker_stats_by_target $1 $2 "golem"
    smt_checker_stats_by_target $1 $2 "eldarica"
    smt_checker_stats_by_target $1 $2 "spacer"
}

function smt_checker_stats_by_smt_solver () {
    # $1 smtChecker

    if [[ "$1" == "tswc" ]]; then
        smt_checker_stats_by_chc_solver $1 "opensmt"
    elif [[ "$1" == "lfsc" ]]; then
        smt_checker_stats_by_chc_solver $1 "cvc5-lfsc"
    elif [[ "$1" == "carcara" ]]; then
        smt_checker_stats_by_chc_solver $1 "cvc5-alethe"
    elif [[ "$1" == "smtinterpol-checker" ]]; then
        smt_checker_stats_by_chc_solver $1 "smtinterpol"
    fi
}

function smt_checker_stats_by_smt_checker () {
    smt_checker_stats_by_smt_solver "tswc"
    smt_checker_stats_by_smt_solver "lfsc"
    smt_checker_stats_by_smt_solver "carcara"
    smt_checker_stats_by_smt_solver "smtinterpol-checker"
}

function smt_checker_stats () {
    smt_checker_stats_by_smt_checker
}

#########################

chc_solver_stats
smt_solver_stats
smt_checker_stats