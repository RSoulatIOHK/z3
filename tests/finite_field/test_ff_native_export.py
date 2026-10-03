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
import ff_native_alethe as whole
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


def check_whole_proofs(args):
    cases = [
        '(declare-const a Bool)(assert a)(assert (not a))',
        '(declare-const x (_ FiniteField 2))(assert (= (ff.add (ff.mul x x) x) #f1m2))',
        '(declare-const x (_ FiniteField 7))(assert (= (ff.mul x x) #f3m7))',
    ]
    # Native circuit preprocessing must export its local case proofs too.
    # These inputs retain arbitrary Boolean selectors and signed field terms.
    for prime in [2, 7, 101]:
        z, o = f'#f0m{prime}', f'#f1m{prime}'
        a, b, c = f'(ite a {o} {z})', f'(ite b {o} {z})', f'(ite c {o} {z})'
        product = f'(ff.mul {a} {b})'
        xor = f'(ff.add {a} {b} (ff.neg (ff.mul #f{2 % prime}m{prime} {product})))'
        mux = f'(ff.add (ff.mul {c} {a}) (ff.mul (ff.add {o} (ff.neg {c})) {b}))'
        for term, boolean in [(product, '(and a b)'), (xor, '(xor a b)'), (mux, '(ite c a b)')]:
            cases.append('(declare-const a Bool)(declare-const b Bool)(declare-const c Bool)' +
                         f'(assert (not (= {term} (ite {boolean} {o} {z}))))')
    for prime in [2, 101]:
        f, z, o = f'(_ FiniteField {prime})', f'#f0m{prime}', f'#f1m{prime}'
        cases.append(f'(declare-const x {f})(declare-const y {f})' +
                     '(assert (= (ff.mul x x) x))(assert (= x y))' +
                     '(assert (not (= (ff.mul y y) y)))')
        cases.append('(declare-const a Bool)(declare-const b Bool)' +
                     f'(declare-const x {f})(declare-const y {f})' +
                     '(assert (= (ff.mul x x) x))(assert (= (ff.mul y y) y))' +
                     f'(assert (= x (ite a {o} {z})))(assert (= y (ite b {o} {z})))' +
                     f'(assert (not (= (ff.mul x y) (ite (and a b) {o} {z}))))')
    # Swapping equality operands must use symmetry without expanding a
    # polynomial whose degree doubles at each shared square.
    field = '(_ FiniteField 101)'
    shared = ''.join(f'(declare-const {x} {field})' for x in ['x', 'y', 'z'])
    shared += f'(define-fun t0 () {field} (ff.add x y))'
    for i in range(1, 5):
        shared += f'(define-fun t{i} () {field} (ff.mul t{i-1} t{i-1}))'
    cases.append(shared + '(assert (= t4 z))(assert (not (= z t4)))')
    # A shared residual-sum proof must be hoisted outside consumer anchors;
    # copying it under each Boolean assignment would unfold its native DAG.
    bits = [f'b{i}' for i in range(8)]
    values = ' '.join(f'(ite {b} #f1m101 #f0m101)' for b in bits)
    cases.append(''.join(f'(declare-const {b} Bool)' for b in bits) +
                 f'(assert (= (ff.add {values}) #f0m101))(assert (or {" ".join(bits)}))')
    for prime in [101, 2**127 - 1]:
        f = f'(_ FiniteField {prime})'; zero = f'#f0m{prime}'; one = f'#f1m{prime}'
        declarations = ''.join(f'(declare-const {x} {f})' for x in ['x', 'y', 'z', 'w', 'u', 'v'])
        cases.append(declarations + '(declare-const flag Bool)' +
                     f'(assert (not (=> (= x (ite flag {one} {zero})) (= (= {one} x) flag))))')
        # Nested assertions and repeated arithmetic exercise input flattening
        # and printer-independent AST identity in the native trace.
        cases.append(declarations + f'(assert (and (and (= x z) (= y w)) '
                     f'(= (ff.mul (ff.add {one} (ff.neg x)) (ff.add {one} (ff.neg y))) (ff.add {one} (ff.neg u))) '
                     f'(= (ff.mul (ff.add {one} (ff.neg z)) (ff.add {one} (ff.neg w))) (ff.add {one} (ff.neg v))) '
                     '(not (= u v))))')
        cases.append(declarations + f'(assert (and (= x {one}) (= y {one}) '
                     f'(not (= (ff.mul x y {one}) {one}))))')
        cases.append(declarations + f'(assert (= y (ff.add x {one})))'
                     f'(assert (= (ff.mul y y) {one}))(assert (not (= y {one})))'
                     f'(assert (not (= y #f{prime-1}m{prime})))')
        cases.append(declarations + f'(assert (or (= x {zero}) (= x {one})))'
                     '(assert (not (= (ff.mul x x) x)))')
        for nonzero in [False, True]:
            body = declarations
            for indicator, inverse in [('z','u'), ('w','v')]:
                factor = f'(ff.add {one} (ff.neg {indicator}))' if nonzero else indicator
                rhs = f'(ff.mul x {inverse})'
                if not nonzero: rhs = f'(ff.add {one} {rhs})'
                body += f'(assert (= (ff.mul x {factor}) {zero}))(assert (= {indicator} {rhs}))'
            cases.append(body + '(assert (not (= z w)))')
    for body in cases:
        text = '(set-logic QF_FF)' + body
        ctx = Context(proof=True); solver = Solver(ctx=ctx)
        solver.set(timeout=10000); solver.from_string(text)
        assert solver.check() == unsat
        proof = solver.proof(); del solver
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp) / 'bundle'
            _, files = whole.write_and_check_bundle(text, proof, directory, args.carcara, args.ffpacheck)
            assert files == whole.artifacts(text, proof)
            whole.check_bundle(text, proof, directory, args.carcara, args.ffpacheck)
            try:
                whole.write_and_check_bundle(text, proof, directory, args.carcara, args.ffpacheck)
            except FileExistsError:
                pass
            else:
                raise AssertionError('fresh-bundle API overwrote an existing certificate')
            # Replacing the original assertions or changing the saved payload
            # must be rejected before invoking external tools.
            rejects(lambda: whole.artifacts('(set-logic QF_FF)(assert true)', proof))
            for name in ['problem.smt2', 'proof.alethe'] + [n for n in files if n.endswith('.pac')][:1]:
                path = directory/name; saved = path.read_text(); path.write_text(saved + '\n; changed\n')
                rejects(lambda: whole.check_bundle(text, proof, directory, args.carcara, args.ffpacheck))
                path.write_text(saved)
    # A supported proof rule cannot justify treating a non-contradictory root
    # as an UNSAT certificate.
    ctx = Context(proof=True); solver = Solver(ctx=ctx)
    solver.from_string('(declare-const x (_ FiniteField 101))(assert (= (ff.add x #f1m101) #f1m101))(assert (not (= x #f0m101)))')
    assert solver.check() == unsat
    proof = solver.proof()
    forged = substitute(proof, (BoolVal(False, ctx), BoolVal(True, ctx)))
    rejects(lambda: whole.artifacts('(assert false)', forged))
    return len(cases)


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
    whole_checked = check_whole_proofs(args)
    print('NATIVE_FF_EXTERNAL_PASS', checked, 'recorded field lemmas;', whole_checked, 'whole native proofs')


if __name__ == '__main__':
    main()
