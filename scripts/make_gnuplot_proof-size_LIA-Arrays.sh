#!/bin/bash

#########################

function make_plot () {
    # $1 chcSolver
    # $2 target

    chcSolver="$1"
    target="$2"

    plotName="plot_proof-size_${chcSolver}_${target}"

    file1="../_proof-size_cvc5-aletheLF_proof_${target}_${chcSolver}.dataPoints"
    #file2="../_proof-size_cvc5-alethe_proof_${target}_${chcSolver}.dataPoints"
    file3="../_proof-size_cvc5-lfsc_proof_${target}_${chcSolver}.dataPoints"
    #file4="../_proof-size_opensmt_proof_${target}_${chcSolver}.dataPoints"
    file5="../_proof-size_smtinterpol_proof_${target}_${chcSolver}.dataPoints"
    file6="../_proof-size_z3_proof_${target}_${chcSolver}.dataPoints"

    filenames="$file1 $file3 $file5 $file6"
    labels="cvc5-AletheLF cvc5-LFSC SMTInterpol Z3"

    if [[ "$chcSolver" == "eldarica" && "$target" == "LIA-Arrays-lin" ]]; then
cat <<EOF >plot.gp # indentation matters here
set terminal epslatex size 7.5cm,6cm color colortext
set output "$plotName.tex"
set lmargin at screen 0.12
set rmargin at screen 0.99
set bmargin at screen 0.10
set tmargin at screen 0.90
set grid ytics
set logscale y
set xrange [0:1000]
set yrange [10:10000000000]
set xtics (0, "250" 250, "500" 500, "750" 750, "1000" 1000)
set ytics ("10 B" 10, "100 B" 100, "1 KB" 1000, "10 KB" 10000, "100 KB" 100000, "1 MB" 1000000, "10 MB" 10000000, "100 MB" 100000000, "1 GB" 1000000000, "10 GB" 10000000000)
set key top left
set key samplen 1
set key box
set key width -7.5
set key height 0.5
set key font ",16"
filenames = "${filenames}"
labels = "${labels[*]}"
plot for [n=1:words(filenames)] word(filenames, n) with linespoints title sprintf("%s %s",'\tiny', word(labels,n))
EOF
    elif [[ "$chcSolver" == "eldarica" && "$target" == "LIA-Arrays-nonlin" ]]; then
cat <<EOF >plot.gp # indentation matters here
set terminal epslatex size 7.5cm,6cm color colortext
set output "$plotName.tex"
set lmargin at screen 0.12
set rmargin at screen 0.99
set bmargin at screen 0.10
set tmargin at screen 0.90
set grid ytics
set logscale y
set xrange [0:10000]
set yrange [10:10000000000]
set xtics (0, "2500" 2500, "5000" 5000, "7500" 7500, "10000" 10000)
set ytics ("10 B" 10, "100 B" 100, "1 KB" 1000, "10 KB" 10000, "100 KB" 100000, "1 MB" 1000000, "10 MB" 10000000, "100 MB" 100000000, "1 GB" 1000000000, "10 GB" 10000000000)
set key top left
set key samplen 1
set key box
set key width -7.5
set key height 0.5
set key font ",16"
filenames = "${filenames}"
labels = "${labels[*]}"
plot for [n=1:words(filenames)] word(filenames, n) with linespoints title sprintf("%s %s",'\tiny', word(labels,n))
EOF
    elif [[ "$chcSolver" == "spacer" && "$target" == "LIA-Arrays-lin" ]]; then
cat <<EOF >plot.gp # indentation matters here
set terminal epslatex size 7.5cm,6cm color colortext
set output "$plotName.tex"
set lmargin at screen 0.12
set rmargin at screen 0.99
set bmargin at screen 0.10
set tmargin at screen 0.90
set grid ytics
set logscale y
set xrange [0:1000]
set yrange [10:10000000000]
set xtics (0, "250" 250, "500" 500, "750" 750, "1000" 1000)
set ytics ("10 B" 10, "100 B" 100, "1 KB" 1000, "10 KB" 10000, "100 KB" 100000, "1 MB" 1000000, "10 MB" 10000000, "100 MB" 100000000, "1 GB" 1000000000, "10 GB" 10000000000)
set key top left
set key samplen 1
set key box
set key width -7.5
set key height 0.5
set key font ",16"
filenames = "${filenames}"
labels = "${labels[*]}"
plot for [n=1:words(filenames)] word(filenames, n) with linespoints title sprintf("%s %s",'\tiny', word(labels,n))
EOF
    elif [[ "$chcSolver" == "spacer" && "$target" == "LIA-Arrays-nonlin" ]]; then
cat <<EOF >plot.gp # indentation matters here
set terminal epslatex size 7.5cm,6cm color colortext
set output "$plotName.tex"
set lmargin at screen 0.12
set rmargin at screen 0.99
set bmargin at screen 0.10
set tmargin at screen 0.90
set grid ytics
set logscale y
set xrange [0:10000]
set yrange [10:10000000000]
set xtics (0, "2500" 2500, "5000" 5000, "7500" 7500, "10000" 10000)
set ytics ("10 B" 10, "100 B" 100, "1 KB" 1000, "10 KB" 10000, "100 KB" 100000, "1 MB" 1000000, "10 MB" 10000000, "100 MB" 100000000, "1 GB" 1000000000, "10 GB" 10000000000)
set key top left
set key samplen 1
set key box
set key width -7.5
set key height 0.5
set key font ",16"
filenames = "${filenames}"
labels = "${labels[*]}"
plot for [n=1:words(filenames)] word(filenames, n) with linespoints title sprintf("%s %s",'\tiny', word(labels,n))
EOF
    fi

    gnuplot plot.gp

    sed -i "s/$plotName/plots\/$plotName/" "$plotName.tex"

    rm -f plot.gp
}

function make_by_target () {
    # $1 chcSolver

    make_plot $1 "LIA-Arrays-lin"
    make_plot $1 "LIA-Arrays-nonlin"
}

function make_by_chcSolver () {
    make_by_target "eldarica"
    #make_by_target "golem"
    make_by_target "spacer"
}

function make_plots () {
    make_by_chcSolver
}

#########################

cd "$(dirname "$0")" # script's folder
cd ..

cd results/logs/plots
make_plots
