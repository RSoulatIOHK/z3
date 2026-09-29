# Does the cvc5 split false-UNSAT have a checked certificate?

**No complete, independently checked certificate was obtained.** This recheck
on September 29 distinguishes failing proof export from rejecting an actual
algebraic derivation. It does not claim that PAC arithmetic checking diagnosed
the underlying solver bug.

The [minimal input](minimal.smt2), reduced from the public CAV24 example
`r_3_32_32_system13.smt2`, asserts over F3:

```
a*b + a + 2*b + 2 = 0
b + 2 = 0
```

Independent enumeration of all nine assignments gives the unique model
`a = b = 1`. Therefore UNSAT is wrong. The four pinned binaries tested here
are cvc5 1.3.3, 1.4.0, main `72f647e`, and the artifact's 1.3.4.dev proof
candidate. All four return SAT in GB mode and false UNSAT in split mode.

| Test | Observed result |
|---|---|
| Split, ordinary solving | False UNSAT in all four binaries |
| Split plus `--check-proofs` | Still false UNSAT, exit 0, in all four |
| Raw proof output (`--proof-format-mode=none`) | Contains `TRUST` steps for `PREPROCESS_FF_BITSUM` and `THEORY_LEMMA ... THEORY_FF` |
| Alethe export in releases/pinned main | Reports `Proof unsupported by Alethe: contains operator ff.add` |
| Artifact candidate with `--ff-proof-pac --proof-granularity=dsl-rewrite` | Reports unsupported `ff.bitsum`, including with simplification disabled |
| `--check-proofs --check-proofs-complete` in 1.4.0, pinned main and artifact candidate | Aborts: incomplete proof due to trusted `PREPROCESS_FF_BITSUM` |
| Sending the emitted error payload to Carcara | Exit 1, `invalid`, parser error on the `error` command in all four |

The strict check rejects **incompleteness** before there is a complete proof
to validate. Ordinary internal checking permits the trusted steps. Exporting
an error message with exit status 0 is not certificate production. The external
checker never reaches PAC arithmetic on these outputs; there is no valid PAC
refutation here. These cases are excluded from checked-proof counts.

The release/main binaries reject `--ff-proof-pac` as an unknown option; only the
artifact candidate supplies that mode. This is why the proof cactus compares
Z3 against that candidate, while the ordinary-solving figures show the other
versions. The paper focuses on the original GB-based decision procedure;
its root-search case splits should not be conflated with `--ff-solver=split`.
See [the paper](https://hanielbarbosa.com/papers/2026fmcad-ffproofs.pdf), Section I.

Separate from this bug, the pinned Carcara PAC bridge has a documented
premise-binding limitation. Z3's pipeline additionally checks original-input
binding and independently replays the exact exported proof. Passing an external
checker that admits holes or does not bind premises would not establish the
original SMT statement. No Lean checking was performed here.

[Commands and complete stdout/stderr](runs.json), [binary hashes and versions](versions.json),
and [external checker receipts](external-checks.json) preserve these observations.
Runs with an invalid exploratory option spelling are excluded from this record.
Example commands (replace binary paths):

```sh
cvc5 --ff-solver=gb minimal.smt2
cvc5 --ff-solver=split --produce-proofs --check-proofs minimal.smt2
cvc5 --ff-solver=split --dump-proofs --proof-format-mode=none minimal.smt2
cvc5 --ff-solver=split --produce-proofs --check-proofs --check-proofs-complete --no-ff-bitsum minimal.smt2
cvc5-paper --ff-solver=split --simplification=none --produce-proofs --dump-proofs --proof-format-mode=alethe --ff-proof-pac --proof-granularity=dsl-rewrite minimal.smt2
```
