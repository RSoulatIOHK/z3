# Native certificate production: replacement contract for PR2

The replacement must produce evidence during the computation that establishes
UNSAT. A second solver that tries to reproduce the result is a baseline, not the
architecture. This document records the work still needed; the opt-in `native`
backend is not yet a certificate for arbitrary native `check-sat` execution.

## Evidence and acceptance

The native certificate backend calls `engine::solve`; it does not reconstruct a second basis schedule. The evidence DAG is independent of its Alethe/PAC serialization. Every input is
bound to an original active assertion or to a checked local hypothesis. Derived
lemmas carry evidence; a dependency set alone is insufficient. Every split must
discharge all alternatives and local hypotheses before its parent closes.
Caching must retain and remap proof references, not merely premise indices.
No unsupported path may emit an apparently complete certificate.

The pipeline can independently select `--backend native` for native algebra and `--boolean-backend native` for native SAT; the legacy choices remain available as comparison baselines. The existing independent original-input checker remains mandatory. External
Carcara/FFPacheck acceptance is reported separately from original-input binding;
new field-specific rules require an implemented checker and cannot be admitted
as holes. Lean checking is not implemented by this work.

## Audited implementation paths

| Native computation | Recording status / required evidence |
| --- | --- |
| Wire elimination (`engine::eliminate`) | Implemented opt-in observer; exact substitution identity, including nonlinear definitions and repeated powers |
| Legacy basis (`engine::basis`, `reduce`, `batch_reduce`) | Implemented opt-in handles for actual scalar and sparse matrix operations, including fused/geobucket and packed/lazy variants |
| F4 basis (`ff_f4.cpp`) | Native engine invokes the recording backend and composes residual-input evidence with preceding substitutions |
| Basis reuse | Still refuses recording; cache entries need replayable, correctly scoped evidence |
| AST preprocessing (`ff_simplify_tactic.cpp`) | Rewrites, solved equations, zero-test rewrites and compact definitions need checked connections to original assertions |
| Uniqueness (`ff_unique_tactic.cpp`, shared `ff_unique.h`) | Ring-only recording implemented for class merges, assigned values, matching linear definitions and zero tests with distinct outputs. Digit injectivity, coincident-output zero tests and Boolean branches still need evidence |
| Bit reasoning (`propagate_bits`, `small_bits`) | Boolean premises, no-wrap bounds and exhaustive assignment coverage must be recorded |
| Finite-field roots and completion | Frobenius axioms, quotient/minimal-polynomial derivations, root completeness and branch closure need proof rules |
| Tiny-field search (`ff_tiny.cpp`) | Domain pruning and exhaustive closure need local explanations |
| Boolean combination | Opt-in pipeline now uses native SAT evidence, independently elaborated into resolution; explicit `incremental` mode retains SAT state/trace across monotone field-lemma additions; integration with `ff_sat_tactic.cpp` and its field-lemma callbacks remains |
| SMT combination (`theory_ff.cpp`) | Explanations must connect field lemmas to equality-engine/SAT premises with scope-safe evidence |
| BV fallback (`ff2bv_tactic.cpp`, theory fallback) | Check encoding equivalence, bit-vector/SAT refutation and premise connection, or explicitly refuse certificate production |

SAT witness probes do not need refutation certificates: they can only establish
SAT after independent model checking. Failed or incomplete probes cannot close
an UNSAT branch. Constant contradictions must retain the derivation of the
constant, including when an earlier transformation made the equation constant.

## Shared uniqueness recording

The native certificate path now invokes the same propagation core as `ff-unique`
before entering `engine::solve`. Each union edge proves `v-parent[v]=0`, each
assigned value proves `root-value=0`, and canonicalization composes these
identities with exact substitution evidence. Old definition keys remain valid
identities and are reduced through the current class state before a merge.
For `a*y+r=0` and `b*z+s=0` with `-r/a=-s/b`, their normalized difference proves
`y-z=0` without globally expanding the circuit.

Zero-test matching also has a ring derivation. For a common monic expression `M`,
let the four proved equations be `A=y-c+alpha*z*M`, `B=t-c+beta*w*M`,
`C=(y-d)*M`, and `D=(t-d)*M`. Then

```
(y-d)*B - (t-d)*A - beta*w*C + alpha*z*D = (d-c)*(y-t).
```

When `d!=c`, multiplication by its inverse proves the equality. When `d==c`,
this identity is insufficient; recording deliberately skips that rule.
Digit inference and branches likewise remain disabled with an observer.
No new trusted checker rule or original-input axiom is introduced.

`ff-certify :backend native :unique false` disables this stage for ablation.
It is not yet a proof of arbitrary `ff-unique` tactic executions or normal
`check-sat`: the shared core's supported subset runs on normalized input
polynomials. Native AST preprocessing and full SAT/theory integration remain
separate open work. A stalled local attempt leaves input equations unchanged;
its work and valid unused DAG nodes remain charged to the same global budget.
The published `auto` reconstruction backend and normal solver defaults are
unchanged.

Regression coverage includes 69 independently checked uniqueness proofs (five
fields through 521 bits, non-unit pivots, repeated powers, reordered equations,
stale keys and zero tests), changed-premise rejection, SAT controls, incremental
scope checks, and C++ checks that close 24-layer circuits and zero-test examples
before elimination/F4/basis search. The complete acceptance suite remains
required after every implementation change.

## Current measured acceptance

The subsequent persistent-SAT milestone passes all 34 acceptance checks. Its
full-corpus run checks 358/390 certificates in both one-shot and persistent
native modes, with exactly the same successful inputs. Persistent search is
12.9% faster by geometric mean on those 358 successes. It produces 360 bundles;
two do not finish checking before the shared 10-second deadline. Published PR2
checks 356 in the same run and harness. Against that baseline, persistence has
six gains and four losses, with a wall-time ratio of 1.008 on 352 common checked
inputs. This improves native proof throughput but is not a coverage-preserving
replacement for published PR2. It remains an explicit experimental option.

A diagnostic propagated polynomial multipliers backward through 108 existing
field-lemma proofs from a slow soundness instance. Exact algebraic cancellation
removed no premises. That measured case does not justify adding a multiplier
compression pass as the next performance change. Field-conflict selection and
the unsupported native inference paths remain open work.

For historical comparison (different run, before persistent SAT):

The shared-uniqueness milestone passes all 33 acceptance checks, plus the two
updated external Boolean suites (34 checked bundles each). On the complete
390-distinct-input FMCAD corpus, at a 10-second whole-pipeline limit and four
workers, native recording checks 355 proofs and published PR2 reconstruction
also checks 355: six gains and six losses. Native recording produces 358 bundles,
but three do not finish checking within the deadline. On 349 common checked
inputs, the geometric mean native/published wall-time ratio is 1.112.
Ordinary solving remains 390/390, with a before/after ratio of 0.997.

The earlier 55-case regression screen improved from 14 checked with the previous
native rewrite to 25 with shared uniqueness; the published baseline checks 20.
That selected screen does not establish a full-corpus advantage. A follow-up
ablation also identifies two cases where enabling uniqueness worsens Boolean
proof search. The implementation remains experimental; these results do not
justify replacing the published default. Detailed runs and figures remain in
the separate research archive, not in the solver source tree.

## Release gates

1. Add an independently checked regression for each supported inference and a
   tampered-premise/witness rejection test. Test scope changes, cancellation,
   resource recovery, SAT controls and all storage variants that carry proofs.
2. Audit every native UNSAT return and goal-closing statement. Require evidence
   at the closing boundary, not a later reconstruction attempt.
3. Run the full existing 390-distinct-input FMCAD corpus at the established
   10-second whole-pipeline limit against the frozen PR2 and cvc5 candidates.
   Report solver completion, proof production and checked proof completion
   separately; preserve all misses and checker failures.
4. Measure normal solving with recording disabled and proof-mode overhead.
   Publish replacement PR2 only with accurate scope, reproducible measurements
   and an explicit accounting of any remaining unsupported path.

Research results and transient proof bundles stay in the separate research
archive; only implementation, regressions and maintained documentation belong
in the solver PR.
