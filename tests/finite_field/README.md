# Finite-field regression tests

The solver tree keeps regression tests and their small, licensed fixtures.
Corpus acquisition, benchmark campaigns, paper sources, figures and experiment
reports are preserved separately. Existing evidence remains available in the
[immutable published snapshot](https://github.com/RSoulatIOHK/z3/tree/0a5210c9009ba5595521c39cefa7ef0a7b1d46aa/tests/finite_field).

## Run the acceptance checks

Python 3.12+, Linux or macOS, and a CMake build are required. The runner uses
that build's Python package and verifies shared-library identity before running
any suite; an installed Z3 cannot accidentally satisfy these tests.

```sh
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release -DZ3_BUILD_PYTHON_BINDINGS=ON
cmake --build build --target z3 test-z3 test-ff-api libz3 build_z3_python_bindings --parallel 2
python3 tests/finite_field/run_tests.py --build build --suite core --out /tmp/ff-core
```

The core selection runs **19 Python suites**, six native groups (`finite_field`,
`ast`, `smt_context`, `smt2print_parse`, `api`, `arith_rewriter`), and the public
C++ API smoke test. The smoke target keeps assertions enabled in Release builds.
Coverage includes exhaustive small-field oracles, SAT models and UNSAT cores,
generic equality rewriting, global/local options, mixed theories, translated
contexts, scopes, cancellation, fallback recovery, F4 and scalar backends.

Certificate validation is a separate explicit selection:

```sh
python3 tests/finite_field/proof_checkers/build.py --out /tmp/ff-checkers
python3 tests/finite_field/run_tests.py --build build --suite proofs \
  --carcara /tmp/ff-checkers/carcara --ffpacheck /tmp/ff-checkers/ffpacheck \
  --out /tmp/ff-proofs
```

The builder verifies the pinned source archive and patch checksums before
building with Cargo/CMake. It requires Rust and GMP; on macOS pass
`--cmake-arg=-DCMAKE_PREFIX_PATH=/opt/homebrew` and, if necessary,
`--cmake-arg=-DCMAKE_CXX_FLAGS=-I/opt/homebrew/include`. Existing local archives
can be supplied with `--archives DIR` (`carcara.tar.gz`, `ffpacheck.tar.gz`).
See [the checker trust boundary](proof_checkers/README.md) for required input
binding and why raw external-checker acceptance alone is insufficient.

The proof suites include native wire-elimination and forced-F4 derivations and exhaustive small-field
oracles, independent DAG/Alethe replay, original-input binding,
external literal and Boolean pipelines, native SAT clause replay, tampered/truncated/wrong-input rejection,
and resource recovery. Missing checkers are an error, not a skipped pass.
Use `--suite all` to combine core and proof selections.

The artifact pipeline replays the polynomial DAG while exporting PAC and
releases each polynomial after its last reference. Its two-million weighted
term storage bound applies to live values, including normalized inputs;
cumulative arithmetic work and output-size bounds still apply. The legacy
standalone replay can retain all values for callers that need them. Tests cover
both modes, repeated operands, non-final roots, dead malformed nodes, unchanged
PAC output, and original-input mismatch. Producer compaction validates structure
without repeating algebraic replay: the complete bundle is checked before
publication, then checked afresh from its stored original input by the bundle
checker. A corruption regression verifies that this boundary cannot publish a
false producer result. PAC export also combines single-use chains into existing
linear-combination inferences, retaining shared intermediate polynomials.
External-checker regressions cover cancellation to zero, repeated references,
and roots preceding unused nodes. Carcara and FFPacheck remain required
acceptance steps.

The optional `--boolean-backend ranges` pipeline mode seeds native SAT search
with certified bit-domain, complement, product, zero-test and bounded-sum lemmas.
It requires `--backend native`. Partial sums are fresh definitions, whose
identities are justified by Alethe `refl`; all arithmetic implications carry
ordinary PAC certificates and keep their original equality premises. No-wrap
zero propagation requires the sum's upper bound to be strictly below the field
modulus. Matching proposes lemmas; it never makes them trusted assumptions.
The JSON certificate uses schema version 3 to reconstruct these definitions
from the original input, while existing version-2 bundles remain supported.
`test_ff_range_proof.py` checks renamed/reordered circuits, complemented outputs,
small-field wraparound SAT counterexamples, conditional constraints, and proof
corruptions through the independent binding checker, FFPacheck and Carcara.

Every invocation requires a new output directory and writes per-suite logs plus
`summary.json`, including commands, statuses, timings and the selected build.
Failures, missing prerequisites and timeouts return a nonzero exit code.
`--jobs` defaults to two and `--timeout` to 300 seconds per suite; timeout stops
the suite's process group, including child solver processes. The CI workflow
runs both selections on Ubuntu Release builds for pull requests and saves the
logs even on failure. `test_ff_runner.py` checks failure handling separately.
These are correctness regressions; the timed public-corpus comparisons remain
separate from CI acceptance and are not silently refreshed by a test run.

The other `test_ff_*.py` files exercise individual algebra, preprocessing,
resource, incremental and certificate features. CLI-based suites accept `--z3`;
external proof tests additionally require the checkers documented in
[proof_checkers/README.md](proof_checkers/README.md). Independent Python proof
checkers intentionally do not share the C++ arithmetic/translation implementation.
`benchmark_qfff.py` remains a small generated benchmark harness; measured public
corpus comparisons and their provenance belong to the research archive.
