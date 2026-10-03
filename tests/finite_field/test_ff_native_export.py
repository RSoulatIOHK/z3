#!/usr/bin/env python3
"""External checking of field lemmas taken from actual default native proofs."""
import argparse
import os
from pathlib import Path
import sys
import tempfile
sys.path.insert(0, str(Path(os.environ.get('Z3_SOURCE_DIR', Path(__file__).resolve().parents[2])) / 'scripts'))
from z3 import *
import ff_native_evidence as native
import ff_certificate as fc


def leaves(proof):
    todo, seen = [proof], set()
    while todo:
        a = todo.pop()
        if a.get_id() in seen: continue
        seen.add(a.get_id())
        if not is_app(a): continue
        if a.decl().kind() == Z3_OP_PR_TH_LEMMA and a.decl().params()[:2] == ['ff', 'pac']:
            yield a
        todo.extend(a.children())


def rejects(action):
    try: action()
    except fc.Invalid: return
    raise AssertionError('corrupted native evidence accepted')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--z3', type=Path, required=True)  # Common acceptance-runner interface.
    parser.add_argument('--carcara', type=Path, required=True)
    parser.add_argument('--ffpacheck', type=Path, required=True)
    args = parser.parse_args()
    checked = 0
    for prime in [7, 101, 2**127-1]:
        ctx = Context(proof=True)
        field = FiniteFieldSort(prime, ctx)
        x = Const('x', field)
        h = Function('h', field, BoolSort(ctx))
        one, neg = FiniteFieldVal(1, field), FiniteFieldVal(prime-1, field)
        solver = Solver(ctx=ctx)
        solver.set(timeout=10000)
        solver.add(x*x == 1, h(x) != h(one), h(x) != h(neg))
        assert solver.check() == unsat
        retained = list(leaves(solver.proof()))
        assert retained
        del solver  # The proof's field leaves must remain independently usable.
        for lemma in retained:
            native.check_lemma(lemma)
            with tempfile.TemporaryDirectory() as tmp:
                directory = Path(tmp)
                files = native.artifacts(lemma)
                for name, text in files.items(): (directory / name).write_text(text)
                native.check_bundle(lemma, directory, args.carcara, args.ffpacheck)
                # Rechecking is bound to this native leaf and exact emitted files,
                # not just to an externally accepted, user-supplied equation set.
                for name in files:
                    (directory / name).write_text(files[name] + '\n; altered\n')
                    rejects(lambda: native.check_bundle(lemma, directory, args.carcara, args.ffpacheck))
                    (directory / name).write_text(files[name])
            forged = substitute(lemma, (lemma.arg(0), BoolVal(False, ctx)))
            rejects(lambda: native.check_lemma(forged))
            evidence = lemma.decl().params()[2]
            root = evidence.arg(1)
            zero = Function('ff-mul', root.sort(), field, root.sort())(root, FiniteFieldVal(0, field))
            bad = evidence.decl()(evidence.arg(0), zero)
            rejects(lambda: native.encode(bad))
            checked += 1
    # Zero-exit tools with missing or misleading markers cannot pass.
    # File/encoding checks above still run before these fake tool responses.
    old_run = native.pp.run
    try:
        with tempfile.TemporaryDirectory() as tmp:
            for name, text in native.artifacts(lemma).items(): (Path(tmp) / name).write_text(text)
            for pac, alethe in [('invalid', 'valid'), ('PROOF CHECK: SUCCEEDED', 'invalid'),
                                ('PROOF CHECK: SUCCEEDED', ''), ('', 'valid')]:
                responses = iter([pac, alethe])
                native.pp.run = lambda *a, **k: {'stdout': next(responses), 'returncode': 0}
                rejects(lambda: native.check_bundle(lemma, tmp, args.carcara, args.ffpacheck))
    finally:
        native.pp.run = old_run
    print('NATIVE_FF_EXTERNAL_PASS', checked, 'recorded field lemmas')


if __name__ == '__main__':
    main()
