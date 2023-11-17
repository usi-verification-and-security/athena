# ATHENA

The modul<ins>**A**</ins>r cons<ins>**T**</ins>rained <ins>**H**</ins>orn clauses mod<ins>**E**</ins>l validatio<ins>**N**</ins> fr<ins>**A**</ins>mework, ATHENA for short, is a framework for the validation of models produced by CHC solvers. It executes the selected CHC solver(s) for a given set of inputs and if a result is SAT it produces and solves the necessary SMT instances to validate the CHC model. Different SMT solvers can be selected for validation, and if the selected solver produces UNSAT proofs capable of being checked, the framework automatically executes the necessary proof checker.

CHC solvers supported: [Eldarica], [Golem], and [Spacer].

SMT solvers supported: [CVC5], [OpenSMT], [SMTInterpol], [veriT], and [Z3].

Proof checkers supported: [Carcara], [LFSC checker], [SMTInterpol checker], and [TSWC].

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

The tools' paths and options, as well as the time and memory limits, can be set in the `run_*.sh` files. Please follow, or update, the current tool paths before executing; the tools' binaries have to be gathered separately.

The input CHC files have to follow the CHC-COMP format. If your files are following a different format, please use the [CHC-COMP formatter] to adjust them.

## Metrics

The classification of the results obtained, e.g., SAT or UNSAT, can be seen by executing `stats_all.sh` in the `scripts` folder. To gather the average sizes of models and proofs, as well as the average runtimes and memory consumptions, execute `logging_stats_all.sh` followed by `python3 avg_stats_all.py [Target]`. To generate plots displaying the sizes of models and proofs execute `make_gnuplot_proof-size.sh`.

## Notes

The framework is currently capable of validating models produced for LIA instances, and has been used in the validation of the benchmarks contained in the [LIA-lin] and [LIA-nonlin] tracks of [CHC-COMP 2022]. The tools used were: [Eldarica v2.0.8], [Golem v0.4.2], [Z3 (Spacer) v4.12.1], [CVC5 v1.0.5], [OpenSMT v2.5.0], [SMTInterpol (checker) v2.5-1259-gf8124b1f], [veriT v2021.06.2-rmx], [Carcara v1.0.0], [LFSC checker 9aab068], and the [latest version of TSWC].

A large part of the [SMT instance generator] was implemented by Fedor Gromov.

## Publication

To know more about the theory behind ATHENA, as well as its applications, have a look at our [iFM23 paper].

[Eldarica]: https://github.com/uuverifiers/eldarica
[Golem]: https://github.com/usi-verification-and-security/golem
[Spacer]: https://github.com/Z3Prover/z3
[CVC5]:https://github.com/cvc5/cvc5
[OpenSMT]: https://github.com/usi-verification-and-security/opensmt
[SMTInterpol]: https://github.com/ultimate-pa/smtinterpol
[veriT]: https://www.verit-solver.org
[Z3]: https://github.com/Z3Prover/z3
[Carcara]: https://github.com/ufmg-smite/carcara
[LFSC checker]: https://github.com/cvc5/LFSC
[SMTInterpol checker]: https://ultimate.informatik.uni-freiburg.de/smtinterpol/proofs.html
[TSWC]: https://verify.inf.usi.ch/certificate-producing-opensmt2
[LIA-lin]: https://github.com/chc-comp/chc-comp22-benchmarks/tree/main/LIA-Lin
[LIA-nonlin]: https://github.com/chc-comp/chc-comp22-benchmarks/tree/main/LIA
[CHC-COMP 2022]: https://chc-comp.github.io/2022
[Eldarica v2.0.8]: https://github.com/uuverifiers/eldarica/releases/tag/v2.0.8
[Golem v0.4.2]: https://github.com/usi-verification-and-security/golem/releases/tag/v0.4.2
[Z3 (Spacer) v4.12.1]: https://github.com/Z3Prover/z3/releases/tag/z3-4.12.1
[CVC5 v1.0.5]: https://github.com/cvc5/cvc5/releases/tag/cvc5-1.0.5
[OpenSMT v2.5.0]: https://github.com/usi-verification-and-security/opensmt/releases/tag/v2.5.0
[SMTInterpol (checker) v2.5-1259-gf8124b1f]: https://ultimate.informatik.uni-freiburg.de/smtinterpol/smtinterpol-2.5-1256-gf8124b1f.jar
[veriT v2021.06.2-rmx]: https://www.verit-solver.org/download/2021.06/verit-2021.06-rmx.tar.gz
[Carcara v1.0.0]: https://github.com/ufmg-smite/carcara/releases/tag/carcara-1.0.0
[LFSC checker 9aab068]: https://github.com/cvc5/LFSC/commit/9aab068dec2c5a9f5f2bf465590005c638078e95
[latest version of TSWC]: https://verify.inf.usi.ch/certificate-producing-opensmt2
[SMT instance generator]: https://github.com/usi-verification-and-security/chc-model-validator/blob/master/scripts/generate_chc_witness_checks.py
[CHC-COMP formatter]: https://github.com/chc-comp/scripts/tree/master/format
[iFM23 paper]: https://doi.org/10.1007/978-3-031-47705-8_4
