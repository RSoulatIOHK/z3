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

The core selection runs **21 Python suites**, eight native groups (`finite_field`,
`ff_solver`, `ff_euf`, `ast`, `smt_context`, `smt2print_parse`, `api`, `arith_rewriter`), and the public
C++ API smoke test. The smoke target keeps assertions enabled in Release builds.
Coverage includes exhaustive small-field oracles, SAT models and UNSAT cores,
generic equality rewriting, global/local options, mixed theories, translated
contexts, scopes, cancellation, fallback recovery, F4 and scalar backends.

`ff_solver` tests the reusable core and rejects corrupted or rebound evidence.
`ff_euf` retains and checks native field hints across persistent scopes.
`test_ff_euf.py` exercises the second consumer with mixed theories, exhaustive
finite-field/UF oracles and online field-proof checking. It requires successful
`ff-pac` replay and rejects fallback to SMT for those field hints; other theories
retain their existing checker behavior. Sequence coverage remains on the legacy
SMT adapter because SAT/EUF has no sequence theory plugin.

External certificate validation is a separate explicit selection:

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

Proof suites exercise independent DAG/Alethe replay, original-input binding,
external literal and Boolean pipelines, tampered/truncated/wrong-input rejection,
and resource recovery. Missing checkers are an error, not a skipped pass.
Use `--suite all` to combine core and proof selections.

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

The upstream-review regressions additionally check that field-valued function
applications retain congruence and pointwise models, and that `ff2bv` preserves
field-valued ITEs. Native tests exercise nested zero-test products (including
multiplicities and premise dependencies) and transitive wire-substitution cores.

The `poseidon_t3.json` fixture contains width-three Poseidon parameters and test
vectors for BN254 and BLS12-381 from the Poseidon implementation in
[HorizenLabs/poseidon2](https://github.com/HorizenLabs/poseidon2/tree/055bde3f4782731ba5f5ce5888a440a94327eaf3/plain_implementations/src/poseidon).
Its header records the source revision and file hashes. `zk_circuits.py` and
`test_zk.py` use this data to test circuit semantics; it is not a solver runtime
dependency. `POSEIDON-LICENSE-MIT` retains the upstream license for this fixture.
