"""Native SAT session lifetime, scope safety, and independent proof replay."""
import argparse
import subprocess
import sys
import time
import tempfile
from pathlib import Path
from unittest.mock import patch
import test_ff_boolean_proof as suite


def field_scopes(binary):
    field = suite.pp.FieldSession(binary)
    pid = field.session.child.pid
    try:
        for p in [7, 2**255-19, 2, 65537, 7]:
            # Reuse the very same symbols at different sorts across scopes.
            # A contradiction from the preceding scope must not justify SAT input.
            prefix = f'(set-logic QF_FF)\n(declare-const x (_ FiniteField {p}))\n'
            zero, one = f'#f0m{p}', f'#f1m{p}'
            sat = prefix + f'(assert (= x {zero}))\n'
            unsat = sat + f'(assert (= x {one}))\n'
            for text, expected in [(unsat, True), (sat, False), (unsat, True)]:
                proof = field.query(text, time.monotonic()+10, 'native')
                assert field.session.child.pid == pid
                assert proof.startswith('(ff-certificate\n') == expected, proof
                if expected:
                    suite.pp.fc.verify(text, proof)
                    suite.reject(lambda: suite.pp.fc.verify(sat, proof))
        suite.reject(lambda: field.query(sat, time.monotonic()-1, 'native'))
    finally:
        field.close()
    assert field.session.child.poll() is not None
    # Multiline framing is bounded and cannot mistake an incomplete response for
    # a completed certificate merely because some newlines have arrived.
    process = suite.pp.NativeSession(binary)
    suite.reject(lambda: process.exchange('(echo "partial")\n', time.monotonic()+.02,
                                         b'\nmissing terminator\n'))
    assert process.closed and process.child.poll() is not None
    # The promoted native default must take the measured persistent paths, with
    # more than one field conflict; one-shot SAT querying is forbidden here.
    pids = []
    query = suite.pp.FieldSession.query
    def record_query(self, *args, **kwargs):
        pids.append(self.session.child.pid)
        return query(self, *args, **kwargs)
    text = suite.source('(assert (or (= x (as ff0 F)) (= x (as ff1 F))))\n'
                        '(assert (= x (as ff2 F)))')
    with patch.object(suite.bp.NativeSearch, 'query', side_effect=AssertionError('unexpected one-shot SAT')):
        with patch.object(suite.pp.FieldSession, 'query', record_query):
            proof = suite.bp.produce(text, binary, 10, backend='native')
    suite.bp.verify_export(text, proof)
    assert len(pids) >= 2 and len(set(pids)) == 1, pids
    print('field session: isolated premises/declarations, changing fields, input binding and incomplete framing checked')


def sessions(binary):
    # A retained UNSAT result/trace must never survive removal of its premise.
    script = """(set-logic QF_UF)
(declare-const a Bool)
(declare-const b Bool)
(assert a)
(ff-boolean-certify :incremental true)
(push)
(assert (not a))
(ff-boolean-certify :incremental true)
(ff-boolean-certify :incremental true)
(pop)
(ff-boolean-certify :incremental true)
(reset-assertions)
(assert (not b))
(ff-boolean-certify :incremental true)
(push)
(assert b)
(ff-boolean-certify :incremental true)
(pop)
(assert (not b))
(ff-boolean-certify :incremental true)
(push)
(assert (= a b))
(ff-boolean-certify :incremental true)
(pop)
(ff-boolean-certify :incremental true)
(reset)
(set-logic QF_UF)
(declare-const a Bool)
(assert (not a))
(ff-boolean-certify :incremental true)
"""
    result = subprocess.run([binary, '-in'], input=script, text=True, capture_output=True, timeout=10)
    assert not result.stderr, result
    all_objects = suite.pp.fc.parse(result.stdout)
    assert sum(x[0] == 'error' for x in all_objects) == 1, all_objects
    objects = [x for x in all_objects if x[0] == 'ff-boolean-result']
    assert [x[2] for x in objects] == ['sat','unsat','unsat','sat','sat','unsat','sat','sat','sat'], objects
    assert objects[-1][6] == ['false'], objects[-1]
    search = suite.bp.IncrementalSearch([(1,2),(-1,2)], binary, time.monotonic()+10)
    try:
        assert search.search()[0]
        pid = search.session.child.pid
        # New variables and clauses must bind correctly after earlier SAT checks.
        search.append((3,), dict(rule='field',clause=[3]))
        assert search.search()[0] and search.session.child.pid == pid
        search.append((-2,), dict(rule='field',clause=[-2]))
        for _ in range(2):
            sat, index = search.search()
            assert not sat and search.clauses[index] == ()
            assert search.session.child.pid == pid
    finally:
        search.close()
    assert search.session.child.poll() is not None
    # Cancellation closes and reaps the owned process even while awaiting input.
    process = suite.pp.NativeSession(binary)
    suite.reject(lambda: process.exchange('(set-logic QF_UF)\n', time.monotonic()+0.02))
    assert process.closed and process.child.poll() is not None
    # An oversized request is rejected before writing and closes its process.
    process = suite.pp.NativeSession(binary)
    suite.reject(lambda: process.exchange('x'*(suite.pp.LIMIT+1), time.monotonic()+1))
    assert process.closed and process.child.poll() is not None
    with tempfile.TemporaryDirectory(prefix='ff-session-transport-') as temp:
        binary_path = Path(temp)/'peer'
        old_limit = suite.pp.LIMIT
        try:
            for body, request, limit in [
                ('import time; time.sleep(5)', 'x'*200000, old_limit),
                ("import os,time; os.write(1,b'x'*65536); time.sleep(5)", '(check-sat)\n', 4096),
                ("import os,time; os.write(2,b'x'*65536); time.sleep(5)", '(check-sat)\n', 4096),
                ('pass', '(check-sat)\n', old_limit),
            ]:
                binary_path.write_text('#!'+sys.executable+'\n'+body+'\n')
                binary_path.chmod(0o700)
                suite.pp.LIMIT = limit
                peer = suite.pp.NativeSession(binary_path)
                suite.reject(lambda: peer.exchange(request, time.monotonic()+0.2))
                assert peer.closed and peer.child.poll() is not None
        finally:
            suite.pp.LIMIT = old_limit
    print('incremental SAT: retained process, growing vocabulary, repeated UNSAT, pop/reset and timeout cleanup checked')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(add_help=False)
    parser.add_argument('--z3', required=True)
    args, _ = parser.parse_known_args()
    sessions(args.z3)
    field_scopes(args.z3)
    sys.argv.extend(['--backend', 'native', '--boolean-backend', 'incremental', '--field-session'])
    suite.main()
