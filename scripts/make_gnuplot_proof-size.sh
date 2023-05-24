#!/bin/bash

#########################

function make_plot () {
    # $1 chcSolver
    # $2 target

    chcSolver="$1"
    target="$2"

    plotName="plot_proof-size_${chcSolver}_${target}"

    file1="../_proof-size_cvc5-alethe_proof_${target}_${chcSolver}.dataPoints"
    file2="../_proof-size_cvc5-lfsc_proof_${target}_${chcSolver}.dataPoints"
    file3="../_proof-size_opensmt_proof_${target}_${chcSolver}.dataPoints"
    file4="../_proof-size_smtinterpol_proof_${target}_${chcSolver}.dataPoints"
    file5="../_proof-size_z3_proof_${target}_${chcSolver}.dataPoints"

    filenames="$file1 $file2 $file3 $file4 $file5"
    labels="CVC5-Alethe CVC5-LFSC OpneSMT SMTInterpol Z3"

    if [[ "$chcSolver" == "eldarica" && "$target" == "LIA-lin" ]]; then
cat <<EOF >plot.gp # indentation matters here
set terminal epslatex size 7.5cm,6cm color colortext
set output "$plotName.tex"
set lmargin at screen 0.12
set rmargin at screen 0.99
set bmargin at screen 0.10
set tmargin at screen 0.90
set grid ytics
set logscale y
set xrange [0:5500]
set yrange [10:1000000000]
set xtics (0, "1 K" 1000, "2 K" 2000, "3 K" 3000, "4 K" 4000, "5 K" 5000)
set ytics ("10 B" 10, "100 B" 100, "1 KB" 1000, "10 KB" 10000, "100 KB" 100000, "1 MB" 1000000, "10 MB" 10000000, "100 MB" 100000000, "1 GB" 1000000000)
set key top left
set key samplen 1
set key box
set key width -3.5
set key height 0.5
set key font ",16"
filenames = "${filenames}"
labels = "${labels[*]}"
plot for [n=1:words(filenames)] word(filenames, n) with linespoints title sprintf("%s %s",'\tiny', word(labels,n))
EOF
    elif [[ "$chcSolver" == "eldarica" && "$target" == "LIA-nonlin" ]]; then
cat <<EOF >plot.gp # indentation matters here
set terminal epslatex size 7.5cm,6cm color colortext
set output "$plotName.tex"
set lmargin at screen 0.12
set rmargin at screen 0.99
set bmargin at screen 0.10
set tmargin at screen 0.90
set grid ytics
set logscale y
set xrange [0:6500]
set yrange [10:1000000000]
set xtics (0, "1.2 K" 1200, "2.4 K" 2400, "3.6 K" 3600, "4.8 K" 4800, "6 K" 6000)
set ytics ("10 B" 10, "100 B" 100, "1 KB" 1000, "10 KB" 10000, "100 KB" 100000, "1 MB" 1000000, "10 MB" 10000000, "100 MB" 100000000, "1 GB" 1000000000)
set key top left
set key samplen 1
set key box
set key width -3.5
set key height 0.5
set key font ",16"
filenames = "${filenames}"
labels = "${labels[*]}"
plot for [n=1:words(filenames)] word(filenames, n) with linespoints title sprintf("%s %s",'\tiny', word(labels,n))
EOF
    elif [[ "$chcSolver" == "golem" && "$target" == "LIA-lin" ]]; then
cat <<EOF >plot.gp # indentation matters here
set terminal epslatex size 7.5cm,6cm color colortext
set output "$plotName.tex"
set lmargin at screen 0.12
set rmargin at screen 0.99
set bmargin at screen 0.10
set tmargin at screen 0.90
set grid ytics
set logscale y
set xrange [0:5500]
set yrange [10:1000000000]
set xtics (0, "1 K" 1000, "2 K" 2000, "3 K" 3000, "4 K" 4000, "5 K" 5000)
set ytics ("10 B" 10, "100 B" 100, "1 KB" 1000, "10 KB" 10000, "100 KB" 100000, "1 MB" 1000000, "10 MB" 10000000, "100 MB" 100000000, "1 GB" 1000000000)
set key top left
set key samplen 1
set key box
set key width -3.5
set key height 0.5
set key font ",16"
filenames = "${filenames}"
labels = "${labels[*]}"
plot for [n=1:words(filenames)] word(filenames, n) with linespoints title sprintf("%s %s",'\tiny', word(labels,n))
EOF
    elif [[ "$chcSolver" == "golem" && "$target" == "LIA-nonlin" ]]; then
cat <<EOF >plot.gp # indentation matters here
set terminal epslatex size 7.5cm,6cm color colortext
set output "$plotName.tex"
set lmargin at screen 0.12
set rmargin at screen 0.99
set bmargin at screen 0.10
set tmargin at screen 0.90
set grid ytics
set logscale y
set xrange [0:23000]
set yrange [10:1000000000]
set xtics (0, "4 K" 4000, "8 K" 8000, "12 K" 12000, "16 K" 16000, "20 K" 20000)
set ytics ("10 B" 10, "100 B" 100, "1 KB" 1000, "10 KB" 10000, "100 KB" 100000, "1 MB" 1000000, "10 MB" 10000000, "100 MB" 100000000, "1 GB" 1000000000)
set key top left
set key samplen 1
set key box
set key width -3.5
set key height 0.5
set key font ",16"
filenames = "${filenames}"
labels = "${labels[*]}"
plot for [n=1:words(filenames)] word(filenames, n) with linespoints title sprintf("%s %s",'\tiny', word(labels,n))
EOF
    elif [[ "$chcSolver" == "spacer" && "$target" == "LIA-lin" ]]; then
cat <<EOF >plot.gp # indentation matters here
set terminal epslatex size 7.5cm,6cm color colortext
set output "$plotName.tex"
set lmargin at screen 0.12
set rmargin at screen 0.99
set bmargin at screen 0.10
set tmargin at screen 0.90
set grid ytics
set logscale y
set xrange [0:12500]
set yrange [10:1000000000]
set xtics (0, "2.2 K" 2200, "4.4 K" 4400, "6.6 K" 6600, "8.8 K" 8800, "11 K" 11000)
set ytics ("10 B" 10, "100 B" 100, "1 KB" 1000, "10 KB" 10000, "100 KB" 100000, "1 MB" 1000000, "10 MB" 10000000, "100 MB" 100000000, "1 GB" 1000000000)
set key top left
set key samplen 1
set key box
set key width -3.5
set key height 0.5
set key font ",16"
filenames = "${filenames}"
labels = "${labels[*]}"
plot for [n=1:words(filenames)] word(filenames, n) with linespoints title sprintf("%s %s",'\tiny', word(labels,n))
EOF
    elif [[ "$chcSolver" == "spacer" && "$target" == "LIA-nonlin" ]]; then
cat <<EOF >plot.gp # indentation matters here
set terminal epslatex size 7.5cm,6cm color colortext
set output "$plotName.tex"
set lmargin at screen 0.12
set rmargin at screen 0.99
set bmargin at screen 0.10
set tmargin at screen 0.90
set grid ytics
set logscale y
set xrange [0:37000]
set yrange [10:1000000000]
set xtics (0, "7 K" 7000, "14 K" 14000, "21 K" 21000, "28 K" 28000, "35 K" 35000)
set ytics ("10 B" 10, "100 B" 100, "1 KB" 1000, "10 KB" 10000, "100 KB" 100000, "1 MB" 1000000, "10 MB" 10000000, "100 MB" 100000000, "1 GB" 1000000000)
set key top left
set key samplen 1
set key box
set key width -3.5
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

    make_plot $1 "LIA-lin"
    make_plot $1 "LIA-nonlin"
}

function make_by_chcSolver () {
    make_by_target "golem"
    make_by_target "eldarica"
    make_by_target "spacer"
}

function make_plots () {
    make_by_chcSolver
}

#########################

cd "$(dirname "$0")" # script's folder
cd ..

cd results/logs
rm -rf plots
mkdir plots
cd plots
make_plots