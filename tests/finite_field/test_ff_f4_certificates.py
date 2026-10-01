#!/usr/bin/env python3
"""Independent replay of forced F4 traces, including matrix and failure paths."""
import argparse
import itertools
import json
from pathlib import Path
import random
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'scripts'))
import ff_certificate as fc
import ff_proof_pipeline as pp


def source(p, equations):
    return (f'(set-logic QF_FF)\n(define-sort F () (_ FiniteField {p}))\n' +
            ''.join(f'(declare-const {v} F)\n' for v in ('x', 'y', 'z')) +
            ''.join(f'(assert {eq})\n' for eq in equations))


def certify(binary, text, options=':backend f4'):
    r = subprocess.run([str(binary), '-in'], input=text + f'(ff-certify {options})\n',
                       text=True, capture_output=True, timeout=15)
    assert r.returncode == 0 and '(error' not in r.stdout, (r.stdout, r.stderr)
    return r.stdout


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--z3', type=Path, required=True)
    args = ap.parse_args()
    checked, unavailable, sat = 0, 0, 0
    # These systems require polynomial products and nontrivial matrix rows;
    # native unit tests also assert that a matrix was actually constructed.
    for p in (7, 65537, 2**61-1, 2**255-19, 2**256-189):
        text = source(p, ['(= (ff.mul x y) (as ff1 F))',
                          '(= (ff.mul x z) (as ff0 F))',
                          '(= (ff.mul y z) (as ff1 F))'])
        proof = certify(args.z3, text)
        fc.verify(text, proof)
        fc.verify_alethe(text, fc.export_alethe(text, proof))
        checked += 1
        for option in (':max_nodes 0', ':max_steps 0'):
            assert 'ff-certificate-unavailable' in certify(args.z3, text, ':backend f4 '+option)
        # Reject altered premises even if the same polynomial shape was solved.
        try:
            fc.verify(text.replace('(ff.mul x z) (as ff0 F)', '(ff.mul x z) (as ff1 F)'), proof)
        except fc.Invalid:
            pass
        else:
            raise AssertionError('F4 proof accepted for changed input')

    rng = random.Random(90210)
    for p in (3, 5, 7):
        for _ in range(60):
            polynomials = []
            for _ in range(rng.randrange(1, 5)):
                terms = [(rng.randrange(1, p), tuple(sorted(rng.choices(range(3), k=rng.randrange(3)))))
                         for _ in range(rng.randrange(1, 6))]
                polynomials.append(terms)
            def evaluate(terms, values):
                total = 0
                for c, mon in terms:
                    for v in mon: c *= values[v]
                    total += c
                return total % p
            exists = any(all(evaluate(poly, a) == 0 for poly in polynomials)
                         for a in itertools.product(range(p), repeat=3))
            equations = []
            for poly in polynomials:
                terms = []
                for c, mon in poly:
                    terms.append('(ff.mul ' + f'(as ff{c} F) ' + ' '.join('xyz'[v] for v in mon) + ')'
                                 if mon else f'(as ff{c} F)')
                expression = terms[0] if len(terms) == 1 else '(ff.add ' + ' '.join(terms) + ')'
                equations.append('(= ' + expression + ' (as ff0 F))')
            text = source(p, equations)
            proof = certify(args.z3, text)
            if proof.startswith('(ff-certificate\n'):
                assert not exists, 'SAT system exported as a refutation'
                fc.verify(text, proof)
                fc.verify_alethe(text, fc.export_alethe(text, proof))
                checked += 1
            else:
                assert 'ff-certificate-unavailable' in proof
                unavailable += 1
            sat += exists
    # The scalar builder retains at most 256 basis rows. These 257 distinct
    # degree-256 monomials hit that structural bound in both scalar schedules;
    # F4 can still reconstruct the contradiction from the same original inputs.
    equations = ['(= (ff.mul ' + ' '.join(['x']*i + ['y']*(256-i)) + ') (as ff0 F))'
                 for i in range(257)]
    equations.append('(= (ff.mul ' + ' '.join(['x']*256) + ') (as ff1 F))')
    wide = source(7, equations)
    assert 'unavailable' in certify(args.z3, wide, ':backend scalar')
    fc.verify(wide, certify(args.z3, wide, ':backend auto'))
    # No new field axiom or model branch can enter this ideal-only profile.
    assert 'unavailable' in certify(args.z3, source(3, ['(= (ff.add (ff.mul x x) (as ff1 F)) (as ff0 F))']))
    huge = source(2**521-1, ['(= x (as ff0 F))', '(= x (as ff1 F))'])
    assert 'unavailable' in certify(args.z3, huge)
    fc.verify(huge, certify(args.z3, huge, ':backend auto'))
    assert ':backend' not in pp.certificate_command(1, 'auto')
    assert ':backend f4' in pp.certificate_command(1, 'f4')
    try: pp.certificate_command(1, 'f4) (exit')
    except fc.Invalid: pass
    else: raise AssertionError('invalid backend accepted')
    print(json.dumps(dict(forced_f4_checked=checked, unavailable=unavailable,
                          exhaustive_sat=sat, exhaustive_cases=180)))


if __name__ == '__main__':
    main()
