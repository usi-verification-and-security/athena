#!/bin/bash

#########################

cd "$(dirname "$0")" # script's folder
cd ..

cd results/logs
rm -rf plots
mkdir plots

../../scripts/make_gnuplot_proof-size_LIA.sh
../../scripts/make_gnuplot_proof-size_LIA-Arrays.sh
