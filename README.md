# ATHENA

The modul<ins>**A**</ins>r cons<ins>**T**</ins>rained <ins>**H**</ins>orn clauses mod<ins>**E**</ins>l validatio<ins>**N**</ins> fr<ins>**A**</ins>mework, ATHENA for short, is a framework for the validation of models produced by CHC solvers. It executes the selected CHC solver(s) for a given set of inputs and if a result is SAT it produces and solves the necessary SMT instances to validate the CHC model. Different SMT solvers can be selected for validation, and if the selected solver produces UNSAT proofs capable of being checked, the framework automatically executes the necessary proof checker.

CHC solvers supported: [Eldarica], [Golem], and [Spacer].

SMT solvers supported: [cvc5], [OpenSMT], [SMTInterpol], [veriT], and [Z3].

Proof checkers supported: [alfc] [^1], [Carcara], [LFSC checker], [SMTInterpol checker], and [TSWC].

## Dependencies

ATHENA has been developed for a Linux environment and requires the following dependencies:

  * [GNU parallel] to execute the selected tools.
  * [Python 3] to gather and display the results obtained.
  * [gnuplot] to produce plots on demand.

## Instructions

To execute the framework, go to the `scripts` folder and execute:

```
evaluate_all.sh [CHC solver] [SMT solver] [SMT mode] [Target] [Num. of threads]
```

`[CHC solver]` is one of `all`, `none`, `eldarica`, `golem`, or `spacer`.

`[SMT solver]` is one of `all`, `none`, `cvc5`, `opensmt`, `smtinterpol`, `verit`, or `z3`.

`[SMT mode]` is one of `all`, `proof`, or `noProof`.

`[Target]` is the folder containing the CHC benchmarks, e.g., `test`.

`[Num. of threads]` is a positive integer.

By default ATHENA searches for the tools it needs in a local folder named `binaries`, containing subfolders for `chc_solvers`, `smt_solvers`, and `smt_checkers`. The tools' paths and options, as well as the time and memory limits, can be set in the `run_*.sh` files. Please follow, or update, the current tool paths before executing; the tools' binaries have to be gathered separately.

The input CHC files have to follow the CHC-COMP format. If your files are following a different format, please use the [CHC-COMP formatter] to adjust them.

### Metrics

To gather the average sizes of models and proofs, as well as the average runtimes and memory consumptions, execute `log_stats_all.sh` followed by `python3 avg_stats_all.py` in the `scripts` folder. After that, the classification of individual tool results obtained, e.g., SAT or UNSAT, can be seen by executing `stats_all.sh`. To generate plots displaying the sizes of proofs execute `make_gnuplot_proof-size.sh`.

To aggregate all individual tool results and to establish the validity of the CHC benchmarks execute `log_results_all.sh`. After that, the aggregate results can be displayed by executing `results_all.sh`.

## Notes

The framework is currently capable of validating models produced for LIA and ALIA benchmarks, and has been used in the validation of the benchmarks from [CHC-COMP 2022] and [CHC-COMP 2024].

* The [2022 benchmarks] used came from the LIA-lin and LIA-nonlin tracks, and have been validated with the following tools: [Eldarica v2.0.8], [Golem v0.4.2], [Z3 (Spacer) v4.12.1], [cvc5 v1.0.5], [OpenSMT v2.5.0], [SMTInterpol (checker) v2.5-1259-gf8124b1f], [veriT v2021.06.2-rmx], [Carcara v1.0.0], [LFSC checker 9aab068], and the [latest version of TSWC].

* The [2024 benchmarks] used came from the LIA-lin, LIA-nonlin, LIA-Arrays-lin, and LIA-Arrays-nonlin tracks, and have been validated with the following tools: [Eldarica v2.1], [Golem v0.5.0], [Z3 (Spacer) v4.13], [cvc5 v1.1.2], [OpenSMT v2.6.0], [SMTInterpol (checker) v2.5-1256-g55d6ba76], [veriT v2021.06.2-rmx], [alfc eca2cbd], [Carcara v1.1.0], [LFSC checker 5a127db], and the [latest version of TSWC].

A large part of the [SMT instance generator] was implemented by Fedor Gromov.

## Publications

To know more about the theory behind ATHENA, as well as its applications, have a look at our papers published at [iFM23] and [FAC].

[^1]: The alfc checker has been recently rebranded *ethos*. According to [@ajreynol] this was only a name change on the checker side, with the codebase carrying over from alfc. Together with this change, however, the relation between cvc5 and alfc/ethos has been refactored and ATHENA has not yet been updated to accommodate for it. For the time being, support is available for [cvc5 v1.1.2] and [alfc eca2cbd].

[@ajreynol]: https://github.com/ajreynol

[GNU parallel]: https://www.gnu.org/software/parallel
[Python 3]: https://www.python.org/downloads
[gnuplot]: http://www.gnuplot.info

[Eldarica]: https://github.com/uuverifiers/eldarica
[Golem]: https://github.com/usi-verification-and-security/golem
[Spacer]: https://github.com/Z3Prover/z3
[cvc5]:https://github.com/cvc5/cvc5
[OpenSMT]: https://github.com/usi-verification-and-security/opensmt
[SMTInterpol]: https://github.com/ultimate-pa/smtinterpol
[veriT]: https://www.verit-solver.org
[Z3]: https://github.com/Z3Prover/z3
[alfc]: https://github.com/cvc5/alfc
[Carcara]: https://github.com/ufmg-smite/carcara
[LFSC checker]: https://github.com/cvc5/LFSC
[SMTInterpol checker]: https://ultimate.informatik.uni-freiburg.de/smtinterpol/proofs.html
[TSWC]: https://verify.inf.usi.ch/certificate-producing-opensmt2

[CHC-COMP formatter]: https://github.com/chc-comp/scripts/tree/master/format
[CHC-COMP 2022]: https://chc-comp.github.io/2022
[CHC-COMP 2024]: https://chc-comp.github.io
[2022 benchmarks]: https://github.com/chc-comp/chc-comp22-benchmarks
[2024 benchmarks]: https://github.com/chc-comp/chc-comp24-benchmarks

[Eldarica v2.0.8]: https://github.com/uuverifiers/eldarica/releases/tag/v2.0.8
[Golem v0.4.2]: https://github.com/usi-verification-and-security/golem/releases/tag/v0.4.2
[Z3 (Spacer) v4.12.1]: https://github.com/Z3Prover/z3/releases/tag/z3-4.12.1
[cvc5 v1.0.5]: https://github.com/cvc5/cvc5/releases/tag/cvc5-1.0.5
[OpenSMT v2.5.0]: https://github.com/usi-verification-and-security/opensmt/releases/tag/v2.5.0
[SMTInterpol (checker) v2.5-1259-gf8124b1f]: https://ultimate.informatik.uni-freiburg.de/smtinterpol/smtinterpol-2.5-1256-gf8124b1f.jar
[veriT v2021.06.2-rmx]: https://www.verit-solver.org/download/2021.06/verit-2021.06-rmx.tar.gz
[Carcara v1.0.0]: https://github.com/ufmg-smite/carcara/releases/tag/carcara-1.0.0
[LFSC checker 9aab068]: https://github.com/cvc5/LFSC/commit/9aab068dec2c5a9f5f2bf465590005c638078e95
[latest version of TSWC]: https://verify.inf.usi.ch/certificate-producing-opensmt2

[Eldarica v2.1]: https://github.com/uuverifiers/eldarica/releases/tag/v2.1
[Golem v0.5.0]: https://github.com/usi-verification-and-security/golem/releases/tag/v0.5.0
[Z3 (Spacer) v4.13]: https://github.com/Z3Prover/z3/releases/tag/z3-4.13.0
[cvc5 v1.1.2]: https://github.com/cvc5/cvc5/releases/tag/cvc5-1.1.2
[OpenSMT v2.6.0]: https://github.com/usi-verification-and-security/opensmt/releases/tag/v2.6.0
[SMTInterpol (checker) v2.5-1256-g55d6ba76]: https://ultimate.informatik.uni-freiburg.de/smtinterpol/smtinterpol-2.5-1256-g55d6ba76.jar
[alfc eca2cbd]: https://github.com/cvc5/alfc/commit/eca2cbd4e27712c35a9111a3c9c517f49c593500
[Carcara v1.1.0]: https://github.com/ufmg-smite/carcara/releases/tag/carcara-1.1.0
[LFSC checker 5a127db]: https://github.com/cvc5/LFSC/commit/5a127dbbcf9a0f822768e783dbf892ee90c435d5

[SMT instance generator]: https://github.com/usi-verification-and-security/chc-model-validator/blob/master/scripts/generate_chc_witness_checks.py
[iFM23]: https://doi.org/10.1007/978-3-031-47705-8_4
[FAC]: https://doi.org/10.1145/3716505
