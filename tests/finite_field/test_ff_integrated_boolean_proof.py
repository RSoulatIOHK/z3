"""Native SAT/theory callbacks, scoped recovery and independent proof binding."""
import argparse
import copy
import sys
import time
from unittest.mock import patch
import test_ff_boolean_proof as suite


def sessions(binary):
    declarations = '''(set-logic ALL)
(declare-const x (_ FiniteField 7))
(declare-const w0 (_ FiniteField 7))
(declare-const w1 (_ FiniteField 7))
(declare-const b0 Bool)
(declare-const b1 Bool)
'''
    registration = '''(assert (= b0 (= x #f0m7)))
(assert (= (not b0) (= (ff.add (ff.mul w0 x) #f6m7) #f0m7)))
(assert (= b1 (= x #f1m7)))
(assert (= (not b1) (= (ff.add (ff.mul w1 (ff.add x #f6m7)) #f6m7) #f0m7)))
'''
    script = declarations + registration + '''(assert b0)
(push)
(assert b1)
(ff-integrated-certify :max_steps 0)
(ff-integrated-certify :max_nodes 1)
(ff-integrated-certify)
(pop)
(ff-integrated-certify)
(push)
(assert b1)
(ff-integrated-certify :max_lemmas 0)
(ff-integrated-certify)
(pop)
(reset-assertions)
'''+registration+'''(assert b1)
(ff-integrated-certify)
(reset)
'''+declarations.replace('FiniteField 7','FiniteField 3')+registration.replace('m7','m3').replace('#f6','#f2')+'''(assert b0)
(assert b1)
(ff-integrated-certify)
'''
    output = suite.pp.run([binary, '-in'], 10, script)['stdout']
    objects = suite.pp.fc.parse(output)
    assert [o[0] for o in objects] == ['ff-integrated-unavailable','ff-integrated-unavailable','ff-integrated-result',
        'ff-integrated-unavailable','ff-integrated-unavailable','ff-integrated-result',
        'ff-integrated-unavailable','ff-integrated-result'], output
    print('integrated scopes: budget recovery, push/pop, reset-assertions and changing fields checked')


def diagnostics(binary):
    script = """(set-logic ALL)
(declare-const x (_ FiniteField 7))
(declare-const b0 Bool)
(declare-const b1 Bool)
(assert (= b0 (= x #f0m7)))
(assert (= b1 (= x #f1m7)))
(assert b0)
(assert b1)
(ff-integrated-certify :max_nodes 1 :diagnostics true)
(ff-integrated-certify :diagnostics true)
"""
    result = suite.pp.run([binary, '-in'], 10, script)
    objects = suite.pp.fc.parse(result['stdout'])
    assert objects[0] == ['ff-integrated-unavailable', 'field-proof-budget/proof-nodes'], objects
    assert objects[1][0] == 'ff-integrated-result', objects
    assert 'ff-theory check=' in result['stderr'] and 'proof_us=' in result['stderr'], result
    # Diagnostics stay out of the certificate protocol and are opt-in.
    quiet = suite.pp.run([binary, '-in'], 10, script.replace(' :diagnostics true', ''))
    assert quiet['stdout'] == result['stdout'] and not quiet['stderr'], quiet
    print('integrated resource reasons, diagnostic stream separation and recovery checked')


def cancellation(binary):
    # Pigeonhole CNF is independent of field algebra and cannot close within
    # this one-millisecond allowance. A later command in the same process must
    # recover without resetting the whole context or accepting a partial trace.
    n = 20
    lines = ['(set-logic ALL)', '(declare-const x (_ FiniteField 7))',
             '(declare-const b Bool)', '(assert (= b (= x #f0m7)))']
    names = [[f'p{i}_{j}' for j in range(n-1)] for i in range(n)]
    lines += [f'(declare-const {p} Bool)' for row in names for p in row]
    lines += ['(assert (or ' + ' '.join(row) + '))' for row in names]
    for j in range(n-1):
        for i in range(n):
            for k in range(i):
                lines.append(f'(assert (or (not {names[i][j]}) (not {names[k][j]})))')
    lines += ['(ff-integrated-certify :timeout 1)', '(reset-assertions)',
              '(assert (= b (= x #f0m7)))', '(assert false)', '(ff-integrated-certify :timeout 1000)']
    objects = suite.pp.fc.parse(suite.pp.run([binary, '-in'], 10, '\n'.join(lines))['stdout'])
    assert objects[0] == ['ff-integrated-unavailable', 'canceled'], objects[0]
    assert len(objects) == 2 and objects[1][0] == 'ff-integrated-result', objects
    print('integrated timer cancellation rejects partial evidence and recovers in the same process')


def corruptions(binary):
    bp, pp = suite.bp, suite.pp
    text = suite.source('(assert (or (= x (as ff0 F)) (= x (as ff1 F))))\n(assert (= x (as ff2 F)))')
    outputs = []
    run = pp.run
    def capture(*args, **kwargs):
        result = run(*args, **kwargs); outputs.append(result['stdout']); return result
    # The entire native conflict sequence must use a single solver invocation.
    with patch.object(pp, 'run', side_effect=capture), patch.object(pp.FieldSession, 'query', side_effect=AssertionError('host field loop')):
        proof = bp.produce(text, binary, 10, backend='native', boolean_backend='integrated')
    assert len(outputs) == 1 and sum(r['rule']=='field' for r in proof['records']) >= 2
    bp.verify_export(text, proof)
    original = pp.fc.parse(outputs[0])[0]
    def rejected(edit):
        bad = copy.deepcopy(original); edit(bad)
        def attempt():
            with patch.object(pp, 'run', return_value={'stdout':pp.fc.sexpr(bad)}):
                result = bp.produce(text, binary, 10, backend='native', boolean_backend='integrated')
            bp.verify_export(text, result)
        suite.reject(attempt)
    rejected(lambda x:x.__setitem__(2,'sat'))
    rejected(lambda x:x[4].append(x[4][-1]))
    rejected(lambda x:x[4].__setitem__(-1,'alien'))
    rejected(lambda x:x.__setitem__(6,[]))
    rejected(lambda x:x[6][0][1].append('999999'))
    rejected(lambda x:x[6][0][1].append(x[6][0][1][0]))
    rejected(lambda x:x.__setitem__(8,[['999999']]))
    def false_algebra(x):
        for lemma in x[6]:
            cert = lemma[3]
            nodes = cert[cert.index(':nodes')+1]
            root_index = cert.index(':root')+1
            nodes.append(['mul',cert[root_index],'2',[]]); cert[root_index] = str(len(nodes)-1)
    rejected(false_algebra)
    print('integrated evidence: one native process, multiple certified conflicts, eight corruption checks')


def watched_replay_cases():
    import random
    rng = random.Random(81237)
    bp = suite.bp
    def oracle(clauses, candidate):
        assigned = {abs(x): x < 0 for x in candidate}
        while True:
            changed = False
            for c in clauses:
                if any(assigned.get(abs(x)) == (x > 0) for x in c): continue
                rest = [x for x in c if abs(x) not in assigned]
                if not rest: return True
                if len(rest) == 1:
                    assigned[abs(rest[0])] = rest[0] > 0; changed = True
            if not changed: return False
    for _ in range(400):
        clauses = [bp.clause(v * rng.choice([-1, 1]) for v in rng.sample(range(1,9), rng.randrange(1,5)))
                   for _ in range(rng.randrange(1,25))]
        search = bp.WatchedSearch(clauses, 'unused', time.monotonic()+10)
        for _ in range(8):
            candidate = bp.clause(v * rng.choice([-1, 1]) for v in rng.sample(range(1,9), rng.randrange(5)))
            expected = oracle([search.clauses[i] for i in search.active], candidate)
            if not expected:
                suite.reject(lambda: search.rup(candidate)); continue
            result = search.rup(candidate)
            assert set(search.clauses[result]) <= set(candidate)
            # Independently replay every recorded resolution, including evidence
            # reused after the active database grows between RUP requests.
            replay = list(clauses)
            for record in search.records:
                assert record['rule'] == 'resolve'
                replay.append(bp.resolve(replay[record['left']], replay[record['right']], record['pivot']))
            assert replay == search.clauses
    print('3200 watched RUP requests checked against a scan oracle and resolution replay')


if __name__ == '__main__':
    watched_replay_cases()
    parser = argparse.ArgumentParser()
    parser.add_argument('--z3', required=True)
    args, _ = parser.parse_known_args()
    sessions(args.z3)
    diagnostics(args.z3)
    cancellation(args.z3)
    corruptions(args.z3)
    sys.argv.extend(['--backend','native','--boolean-backend','integrated'])
    suite.main()
