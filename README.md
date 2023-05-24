# Validation framework for CHC models

This is a modular framework for the validation of models produced by CHC solvers. It executes the selected CHC solver(s) for a given set of inputs and if a result is SAT it produces and solves the necessary SMT instances to validate the CHC model. Different SMT solvers can be selected for validation, and if the selected solver produces UNSAT proofs capable of being checked, the framework automatically executes the necessary proof checker.

CHC solvers supported: [Eldarica], [Golem], and [Spacer].

SMT solvers supported: [CVC5], [OpenSMT], [SMTInterpol], [veriT], and [Z3].

Proof checkers supported: [Carcara], [LFSC checker], [SMTInterpol checker], and [TSWC].

## Instructions

TODO

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