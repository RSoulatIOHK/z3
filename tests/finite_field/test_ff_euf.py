#!/usr/bin/env python3
"""Shared FF core through the SAT/EUF consumer, including online PAC checking."""
import os
import subprocess
import sys
from z3 import *
from test_ff_combination import examples, finite_domains, incremental, exhaustive_uf, check


def factory(proof=False):
    return With(Tactic('sat'), euf=True, **{'smt.proof.check': proof}).solver()


def run(proof):
    make = lambda: factory(proof)
    # The SAT/EUF frontend has no sequence plugin. Its existing sequence
    # incompleteness is not hidden or routed to the legacy SMT solver here.
    examples(make, include_sequences=False)
    incremental(make)
    exhaustive_uf(make)
    if not proof:
        finite_domains(make)
    for prime in [101, 2**127-1]:
        F = FiniteFieldSort(prime)
        x, y = Consts('euf_large_x euf_large_y', F)
        h = Function('euf_observer', F, IntSort())
        check(make, [x*x == 1, h(x) != h(FiniteFieldVal(1,F)),
                     h(x) != h(FiniteFieldVal(prime-1,F))], unsat, 'large shared roots')
        check(make, [y == x*x, x == 3, h(y) == 11], sat, 'large field model')
    print('FF_EUF_PASS', flush=True)


if __name__ == '__main__':
    if '--proof-worker' in sys.argv:
        run(True)
    else:
        run(False)
        # The online checker logs a miss before falling back to another SMT
        # solve. Such fallback must never masquerade as checked FF evidence.
        child = subprocess.run([sys.executable, __file__, '--proof-worker'],
                               text=True, capture_output=True, timeout=120)
        assert child.returncode == 0 and 'FF_EUF_PASS' in child.stdout, child.stdout + child.stderr
        assert '+ff-pac ' in child.stdout, child.stdout
        assert '-ff-pac ' not in child.stdout, child.stdout
        assert '(error' not in child.stdout and 'did not verify' not in child.stdout and 'not verified' not in child.stdout, child.stdout
        print('FF_EUF_PROOFS_PASS')
