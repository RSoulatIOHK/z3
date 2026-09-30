"""Exercise the shared native elimination path with independent certificate oracles."""
import argparse
import subprocess
import random
import test_ff_certificates as suite

_original_run = suite.run

def native_run(binary, text, options=''):
    return _original_run(binary, text, ':backend native ' + options)

def branch_cases(binary):
    checked = 0
    rng = random.Random(20261001)
    for p in [2, 7, 65537, 2**255-19, 2**521-1]:
        equations = ['(= (ff.mul x x) x)',
                     '(= (ff.mul x y) (as ff1 F))',
                     '(= (ff.mul (ff.add (as ff1 F) (ff.neg x)) z) (as ff1 F))']
        declarations = '\n'.join(f'(declare-const {v} F)' for v in ['x','y','z','w'])
        for _ in range(4):
            order = rng.sample(equations, len(equations))
            text = suite.source(p, order, declarations=declarations)
            proof = native_run(binary, text)
            suite.check_both(text, proof); checked += 1
            suite.rejected(suite.checker.verify, suite.source(p, order[:-1], declarations=declarations), proof)
        # The bit-domain premise may be attached to a different class member.
        alias = ['(= (ff.mul w w) w)', '(= w x)'] + equations[1:]
        text = suite.source(p, alias, declarations=declarations)
        suite.check_both(text, native_run(binary,text)); checked += 1
        # Only one branch closes. Its local contradiction must not escape.
        sat = suite.source(p, equations[:2], declarations=declarations)
        assert '(ff-certificate\n' not in native_run(binary,sat), sat
        if p > 3:
            wrong_domain = suite.source(p, ['(= (ff.mul x x) (as ff1 F))']+equations[1:], declarations=declarations)
            assert '(ff-certificate\n' not in native_run(binary,wrong_domain), wrong_domain
            bits = [f'(= (ff.mul {v} {v}) {v})' for v in ['x','y','z']]
            nested = suite.source(p, bits+['(= (ff.add x y z) (as ff4 F))'], declarations=declarations)
            proof = native_run(binary,nested)
            suite.check_both(nested,proof); checked += 1
            # Branches must discharge under the actual modulus and premises.
            suite.rejected(suite.checker.verify,nested.replace('(as ff4 F)','(as ff2 F)'),proof)
        # A failed bounded attempt cannot poison the next proof context.
        text = suite.source(p, equations, declarations=declarations)
        transcript = _original_run(binary, text+'(ff-certify :backend native :max_nodes 4)\n', ':backend native')
        assert transcript.startswith('(ff-certificate-unavailable budget)\n'), transcript
        suite.check_both(text,transcript.split('\n',1)[1])
        scoped = suite.source(p, equations[:2], declarations=declarations)
        scoped += f'(push)\n(assert {equations[2]})\n(ff-certify :backend native)\n(pop)\n'
        transcript = native_run(binary,scoped)
        assert transcript.count('(ff-certificate\n') == 1 and transcript.endswith('(ff-certificate-unavailable no-polynomial-refutation)\n'), transcript
    # A disconnected Boolean component can leave branching inconclusive even
    # when the remaining nonlinear component has a unit ideal. Native basis
    # fallback must retain the original scope and discard temporary assumptions.
    declarations = '\n'.join(f'(declare-const {v} F)' for v in ['x','y']+[f'b{i}' for i in range(6)])
    equations = [f'(= (ff.mul b{i} b{i}) b{i})' for i in range(6)] + [
        '(= (ff.mul x x) (as ff1 F))', '(= (ff.mul x y) (as ff1 F))', '(= (ff.mul y y) (as ff2 F))']
    text = suite.source(7,equations,declarations=declarations)
    suite.check_both(text,native_run(binary,text))
    print(f'{checked} discharged Boolean-branch proofs checked, including nested/aliased bits and SAT/budget controls')

def uniqueness_cases(binary):
    rng = random.Random(20260930)
    checked = 0
    for prime in [2, 7, 65537, 2**255 - 19, 2**521 - 1]:
        c = 1 if prime == 2 else prime - 2
        declarations = '\n'.join(f'(declare-const {v} F)' for v in
                                 ['u'] + [f'{side}{i}' for side in ['a', 'b'] for i in range(17)])
        equations = ['(= a0 b0)']
        for i in range(1, 17):
            # Constant, linear and cubic terms exercise canonicalization through
            # shared variables, repeated powers and differently scaled pivots.
            for side, pivot in [('a', c), ('b', 1)]:
                v, w = f'{side}{i}', f'{side}{i-1}'
                rhs = f'(ff.add (ff.mul {w} {w} {w}) {w} (as ff1 F))'
                equations.append(f'(= (ff.mul (as ff{pivot} F) {v}) (ff.mul (as ff{pivot} F) {rhs}))')
        equations.append('(= (ff.mul (ff.add a16 (ff.neg b16)) u) (as ff1 F))')
        for order in [equations, list(reversed(equations)), rng.sample(equations, len(equations))]:
            text = suite.source(prime, order, declarations=declarations)
            proof = native_run(binary, text)
            suite.check_both(text, proof)
            # Breaking one link gives a different problem, not a valid proof of
            # the old output relation. Premise binding must reject that reuse.
            suite.rejected(suite.checker.verify, text.replace('(= a0 b0)', '(= a0 (ff.add b0 (as ff1 F)))'), proof)
            checked += 1
    # Values can precede/follow a merge; old function keys may outlive several
    # representative changes. Vary equation ordering to exercise those cases.
    for p in [2, 7, 65537]:
        equations = ['(= x z)', '(= y z)', '(= w (ff.mul x x))',
                     '(= t (ff.mul y y))', '(= z (as ff1 F))',
                     '(= (ff.mul (ff.add w (ff.neg t)) u) (as ff1 F))']
        declarations = '\n'.join(f'(declare-const {v} F)' for v in ['x','y','z','w','t','u'])
        for _ in range(8):
            order = rng.sample(equations, len(equations))
            text = suite.source(p, order, declarations=declarations)
            suite.check_both(text, native_run(binary, text))
            checked += 1
        # A SAT control uses different function constants. It has the concrete
        # witness x=y=z=1, w=1, t=2, u=-1 in each field (including characteristic 2).
        sat = suite.source(p, [e.replace('(= t (ff.mul y y))',
                                        '(= t (ff.add (ff.mul y y) (as ff1 F)))') for e in equations],
                           declarations=declarations)
        assert '(ff-certificate\n' not in native_run(binary, sat), sat
    # IsZero-style dependencies use a four-equation identity. The multiplier
    # variables need not be equal, and the two S expressions may be scaled.
    for p in [2, 7, 65537, 2**255 - 19, 2**521 - 1]:
        c0, d, alpha = (1, 0, 1) if p == 2 else (3, 5, p-2)
        S = '(ff.add (ff.mul x x) (ff.neg x))'
        equations = [f'(= y (ff.add (as ff{c0} F) (ff.neg (ff.mul z {S}))))',
                     f'(= (ff.mul (ff.add y (as ff{-d} F)) {S}) (as ff0 F))',
                     f'(= t (ff.add (as ff{c0} F) (ff.neg (ff.mul (as ff{alpha} F) w {S}))))',
                     f'(= (ff.mul (as ff{alpha} F) (ff.add t (as ff{-d} F)) {S}) (as ff0 F))',
                     '(= (ff.mul (ff.add y (ff.neg t)) u) (as ff1 F))']
        declarations = '\n'.join(f'(declare-const {v} F)' for v in ['x','y','z','w','t','u'])
        for _ in range(6):
            order = rng.sample(equations, len(equations))
            text = suite.source(p, order, declarations=declarations)
            proof = native_run(binary, text)
            suite.check_both(text, proof)
            # Dropping either zero-test premise invalidates the purported local
            # inference; the checker must still bind every original premise.
            suite.rejected(suite.checker.verify, suite.source(p, order[:-1], declarations=declarations), proof)
            checked += 1
        sat_eqs = equations.copy()
        sat_eqs[2] = sat_eqs[2].replace(f'(as ff{c0} F)', f'(as ff{c0+1} F)', 1)
        sat = suite.source(p, sat_eqs, declarations=declarations)
        assert '(ff-certificate\n' not in native_run(binary, sat), sat
    # Assertion scopes do not retain class edges/proof IDs between invocations.
    text = suite.source(7, ['(= x y)'])
    command = text + '(push)\n(assert (= (ff.add x (ff.neg y)) (as ff1 F)))\n'
    command += '(ff-certify :backend native)\n(pop)\n(ff-certify :backend native)\n'
    result = subprocess.run([binary, '-in'], input=command, text=True, capture_output=True, timeout=15)
    assert result.returncode == 0 and not result.stderr, result
    assert result.stdout.count('(ff-certificate\n') == 1 and 'unavailable' in result.stdout, result.stdout
    print(f'{checked} native uniqueness proofs checked; SAT, changed-premise and incremental-scope controls passed')

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--z3', required=True)
    args = parser.parse_args()
    branch_cases(args.z3)
    uniqueness_cases(args.z3)
    count = 0
    for prime in [2, 7, 65537, 2**255 - 19, 2**521 - 1]:
        # A non-unit pivot fixes x=y^2+1. Cubic occurrences of x exercise
        # every term of the geometric-series substitution witness.
        c = 1 if prime == 2 else 2
        value = '(ff.add (ff.mul y y) (as ff1 F))'
        cube = f'(ff.mul {value} {value} {value})'
        equations = [f'(= (ff.mul (as ff{c} F) x) (ff.mul (as ff{c} F) {value}))',
                     f'(= (ff.mul x x x) (ff.add {cube} (as ff1 F)))']
        for ordered in [equations, list(reversed(equations))]:
            text = suite.source(prime, ordered)
            proof = native_run(args.z3, text)
            suite.check_both(text, proof)
            suite.rejected(suite.checker.verify, suite.source(prime, ordered[:1]), proof)
            count += 1
    print(f'{count} nonlinear, repeated-power and non-unit-pivot certificates checked')
    variants = [[], ['batch=false'], ['batch=false', 'fused_reduction=true'],
                ['batch=false', 'geobucket=true'], ['batch=true', 'compact_matrix=true'],
                ['batch=true', 'lazy_matrix=true'], ['batch=true', 'sparse_matrix_reducers=true'],
                ['batch=true', 'compact_matrix=true', 'lazy_matrix=true', 'sparse_matrix_reducers=true',
                 'sugar_pairs=true', 'gm_pairs=true', 'div_masks=true', 'small_coefficients=true']]
    for prime in [2, 7, 65537, 2**255 - 19]:
        text = suite.source(prime, ['(= (ff.mul x x) (as ff1 F))',
                                  '(= (ff.mul x y) (as ff1 F))',
                                  '(= (ff.mul y y) (as ff2 F))'])
        for variant in variants:
            result = subprocess.run([args.z3, 'smt.ff.f4=false'] + ['smt.ff.' + option for option in variant] + ['-in'],
                                    input=text + '(ff-certify :backend native)\n',
                                    text=True, capture_output=True, timeout=15)
            assert result.returncode == 0 and not result.stderr, result
            suite.check_both(text, result.stdout)
    print(f'{len(variants)*4} native scalar/matrix/storage variants independently checked')
    for prime in [7, 65537, 2**255 - 19]:
        text = suite.source(prime, [
            '(= x (ff.add (ff.mul z z) (as ff1 F)))',
            '(= (ff.mul x x) (as ff1 F))',
            '(= (ff.mul x y) (as ff1 F))',
            '(= (ff.mul y y) (as ff2 F))'],
            extra='(declare-const z F)')
        proof = native_run(args.z3, text)
        suite.check_both(text, proof)
        suite.rejected(suite.checker.verify, text.replace('(as ff2 F)', '(as ff1 F)'), proof)
    print('3 composed elimination/F4 certificates independently checked')
    suite.run = native_run
    suite.main()
