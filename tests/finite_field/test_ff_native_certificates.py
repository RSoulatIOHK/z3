"""Exercise the shared native elimination path with independent certificate oracles."""
import argparse
import subprocess
import random
import copy
import test_ff_certificates as suite
import ff_proof_pipeline as pipeline

_original_run = suite.run
_original_check_both = suite.check_both

def check_both(text, proof):
    result = _original_check_both(text, proof)
    _original_check_both(text, suite.checker.try_balance_certificate(proof))
    fc = suite.checker
    _, cert, values = fc.verify(text, proof)
    streamed, pac = pipeline.verified_pac(fc.Problem(text), proof, compact=False)
    assert cert == streamed and pac == pipeline.export_pac(cert, values)
    return result

suite.check_both = check_both

def balancing_cases():
    fc = suite.checker
    # A valid but needlessly expensive proof: hundreds of expanding prefix
    # sums cancel back to the original input 1=0. Rebalancing must respect the
    # existing checker limit, rather than increase it to accept the raw trace.
    text = suite.source(7, ['(= (as ff1 F) (as ff0 F))'])
    nodes = [['input','0']]; root = 0
    for coefficient in [1,6]:
        for degree in range(1,251):
            term = len(nodes); nodes.append(['mul','0',str(coefficient),['0']*degree])
            index = len(nodes); nodes.append(['add',str(root),str(term)]); root = index
    cert = ['ff-certificate',':version','1',':modulus','7',':variables',['x'],
            ':inputs',[[['1']]],':nodes',nodes,':root',str(root)]
    raw = fc.sexpr(cert)
    suite.rejected(fc.verify,text,raw)
    observed = []
    result = fc.verify_problem(fc.Problem(text), raw, retain_values=False,
                               on_node=lambda c, i, v: observed.append((i, len(v))))
    assert result[2] is None and len(observed) == len(nodes)
    assert observed[-1] == (root, 1)
    suite.rejected(fc.verify_problem, fc.Problem(text.replace('ff1','ff0')), raw)
    # A non-final root and repeated operand need independent lifetime handling.
    tiny = copy.deepcopy(cert)
    tiny[tiny.index(':nodes')+1] = [['input','0'], ['add','0','0'], ['mul','1','4',[]], ['mul','0','2',[]]]
    tiny[tiny.index(':root')+1] = '2'
    _, pac = pipeline.verified_pac(fc.Problem(text), fc.sexpr(tiny), compact=False)
    assert pac == 'm 7;\na 1 1;\nl 2 1*(1) + 1*(1), 2;\nl 3 2*(4), 1;\nunsat\n'
    _, compact_pac = pipeline.verified_pac(fc.Problem(text), fc.sexpr(tiny))
    assert compact_pac == 'm 7;\na 1 1;\nl 2 1*(1), 1;\nunsat\n'
    def stream(problem, proof):
        return pipeline.verified_pac(fc.Problem(problem), proof)
    suite.rejected(stream, text.replace('ff1','ff0'), fc.sexpr(tiny))
    # Dead nodes still have to be well-formed and arithmetically valid.
    for replacement in [['add','4','0'], ['mul','0','7',[]], ['input','1'], ['hole']]:
        bad = copy.deepcopy(tiny); bad[bad.index(':nodes')+1][-1] = replacement
        suite.rejected(stream, text, fc.sexpr(bad))
    wrong = copy.deepcopy(tiny); wrong[wrong.index(':root')+1] = '3'
    suite.rejected(stream, text, fc.sexpr(wrong))
    balanced = fc.balance_certificate(raw)
    _original_check_both(text,balanced)
    suite.rejected(fc.verify,text.replace('ff1','ff0'),balanced)
    for replacement in [['add','1','0'],['mul','0','0',[]],['input','2'],['hole']]:
        bad = copy.deepcopy(cert); bad[bad.index(':nodes')+1][1] = replacement
        suite.rejected(fc.balance_certificate,fc.sexpr(bad))
        suite.rejected(fc.read_certificate,fc.sexpr(bad))
    print('proof balancing: retained-term recovery, unchanged-input binding and malformed/cyclic nodes checked')

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
    # Two Boolean inputs select four values of a shared arithmetic circuit.
    # The closed form agrees on that domain but is not the same polynomial:
    # (x+y)^(2^depth) = x+y+(2^(2^depth)-2)*x*y for x,y in {0,1}.
    # Nested discharge must compose multipliers across nonlinear wire proofs.
    for p in [7, 65537, 2**255-19]:
        for depth in [2, 3]:
            names = ['x','y','u']+[f'a{i}' for i in range(depth+1)]
            declarations = '\n'.join(f'(declare-const {v} F)' for v in names)
            equations = ['(= (ff.mul x x) x)', '(= (ff.mul y y) y)', '(= a0 (ff.add x y))']
            equations += [f'(= a{i} (ff.mul a{i-1} a{i-1}))' for i in range(1,depth+1)]
            coefficient = (2**(2**depth)-2) % p
            rhs = f'(ff.add x y (ff.mul (as ff{coefficient} F) x y))'
            equations += [f'(= (ff.mul (ff.add a{depth} (ff.neg {rhs})) u) (as ff1 F))']
            text = suite.source(p,equations,declarations=declarations)
            proof = native_run(binary,text)
            suite.check_both(text,proof); checked += 1
            suite.rejected(suite.checker.verify, suite.source(p,equations[1:],declarations=declarations),proof)
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
    balancing_cases()
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
