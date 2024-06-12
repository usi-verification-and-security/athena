#!/bin/bash

specificTarget=$1  # e.g., test
printForLatex=false # print in the format of a Latex table

#########################

function chc_solver_stats_call () {
    # $1 target
    # $2 chcSolver

    ./stats_chc_solver.sh $2 $1 $printForLatex
}

function chc_solver_stats_by_chc_solver () {
    # $1 target

    if [[ "$printForLatex" == "true" ]]; then
        echo "        \multirow{4}{*}{\begin{tabular}[c]{@{}c@{}} $1 \\\\ (X benchmarks) \end{tabular}}"
    fi

    chc_solver_stats_call $1 "eldarica"
    chc_solver_stats_call $1 "golem"    
    chc_solver_stats_call $1 "spacer"
}


function chc_solver_stats_by_target () {
    if [[ "$specificTarget" != "" ]]; then
        chc_solver_stats_by_chc_solver $specificTarget
    else
        chc_solver_stats_by_chc_solver "LIA-lin"
        chc_solver_stats_by_chc_solver "LIA-nonlin"
        chc_solver_stats_by_chc_solver "LIA-Arrays-lin"
        chc_solver_stats_by_chc_solver "LIA-Arrays-nonlin"
    fi
}

function chc_solver_stats () {
    chc_solver_stats_by_target
}

#########################

function smt_solver_stats_call () {
    # $1 smtMode
    # $2 target
    # $3 chcSolver
    # $4 smtSolver

    ./stats_smt_solver.sh $4 $1 $2 $3 $printForLatex
}

function smt_solver_stats_by_smt_solver () {
    # $1 smtMode
    # $2 target
    # $3 chcSolver

    if [[ "$printForLatex" == "true" ]]; then
        if [[ "$3" == "golem" ]]; then
            chcSolverLatex="\golem{}"
        elif [[ "$3" == "eldarica" ]]; then
            chcSolverLatex="\eldarica{}"
        elif [[ "$3" == "spacer" ]]; then
            chcSolverLatex="\spacer{}"
        fi

        echo "        \multirow{4}{*}{\begin{tabular}[c]{@{}c@{}} \\\\ $2 \\\\ $chcSolverLatex \\\\ (X instances) \end{tabular}}"
    fi

    if [[ "$1" == "proof" ]]; then
        smt_solver_stats_call $1 $2 $3 "cvc5-lfsc"
        smt_solver_stats_call $1 $2 $3 "cvc5-alethe"
        smt_solver_stats_call $1 $2 $3 "cvc5-aletheLF"
    elif [[ "$1" == "noProof" ]]; then
        smt_solver_stats_call $1 $2 $3 "cvc5"
    fi

    smt_solver_stats_call $1 $2 $3 "opensmt"
    smt_solver_stats_call $1 $2 $3 "smtinterpol"
    smt_solver_stats_call $1 $2 $3 "verit"
    smt_solver_stats_call $1 $2 $3 "z3"    
}

function smt_solver_stats_by_chc_solver () {
    # $1 smtMode
    # $2 target

    smt_solver_stats_by_smt_solver $1 $2 "eldarica"
    smt_solver_stats_by_smt_solver $1 $2 "golem"
    smt_solver_stats_by_smt_solver $1 $2 "spacer"
}

function smt_solver_stats_by_target () {
    # $1 smtMode

    if [[ "$specificTarget" != "" ]]; then
        smt_solver_stats_by_chc_solver $1 $specificTarget
    else
        smt_solver_stats_by_chc_solver $1 "LIA-lin"
        smt_solver_stats_by_chc_solver $1 "LIA-nonlin"
        smt_solver_stats_by_chc_solver $1 "LIA-Arrays-lin"
        smt_solver_stats_by_chc_solver $1 "LIA-Arrays-nonlin"
    fi
}

function smt_solver_stats_by_smt_mode () {
    smt_solver_stats_by_target "noProof"
    smt_solver_stats_by_target "proof"
}

function smt_solver_stats () {
    smt_solver_stats_by_smt_mode
}

#########################

function smt_checker_stats_call () {
    # $1 target
    # $2 chcSolver
    # $3 smtChecker
    # $4 smtSolver

    ./stats_smt_checker.sh $3 $4 $1 $2 $printForLatex
}

function smt_checker_stats_by_smt_solver () {
    # $1 target
    # $2 chcSolver
    # $3 smtChecker

    if [[ "$3" == "alfc" ]]; then
        smt_checker_stats_call $1 $2 $3 "cvc5-aletheLF"
    elif [[ "$3" == "carcara" ]]; then
        smt_checker_stats_call $1 $2 $3 "cvc5-alethe"
    elif [[ "$3" == "lfsc" ]]; then
        smt_checker_stats_call $1 $2 $3 "cvc5-lfsc"
    elif [[ "$3" == "smtinterpol-checker" ]]; then
        smt_checker_stats_call $1 $2 $3 "smtinterpol"
    elif [[ "$3" == "tswc" ]]; then
        smt_checker_stats_call $1 $2 $3 "opensmt"
    fi
}

function smt_checker_stats_by_smt_checker () {
    # $1 target
    # $2 chcSolver

    if [[ "$printForLatex" == "true" ]]; then
        if [[ "$2" == "golem" ]]; then
            chcSolverLatex="\golem{}"
        elif [[ "$2" == "eldarica" ]]; then
            chcSolverLatex="\eldarica{}"
        elif [[ "$2" == "spacer" ]]; then
            chcSolverLatex="\spacer{}"
        fi

        echo "        \multirow{4}{*}{\begin{tabular}[c]{@{}c@{}} \\\\ $1 \\\\ $chcSolverLatex \end{tabular}}"
    fi

    smt_checker_stats_by_smt_solver $1 $2 "alfc"
    smt_checker_stats_by_smt_solver $1 $2 "carcara"
    smt_checker_stats_by_smt_solver $1 $2 "lfsc"
    smt_checker_stats_by_smt_solver $1 $2 "smtinterpol-checker"
    smt_checker_stats_by_smt_solver $1 $2 "tswc"
}

function smt_checker_stats_by_chc_solver () {
    # $1 target

    smt_checker_stats_by_smt_checker $1 "eldarica"
    smt_checker_stats_by_smt_checker $1 "golem"
    smt_checker_stats_by_smt_checker $1 "spacer"
}

function smt_checker_stats_by_target () {
    if [[ "$specificTarget" != "" ]]; then
        smt_checker_stats_by_chc_solver $specificTarget
    else
        smt_checker_stats_by_chc_solver "LIA-lin"
        smt_checker_stats_by_chc_solver "LIA-nonlin"
        smt_checker_stats_by_chc_solver "LIA-Arrays-lin"
        smt_checker_stats_by_chc_solver "LIA-Arrays-nonlin"
    fi
}

function smt_checker_stats () {
    smt_checker_stats_by_target
}

#########################

chc_solver_stats
smt_solver_stats
smt_checker_stats
