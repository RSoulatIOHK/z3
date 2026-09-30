"""Native SAT session lifetime, scope safety, and independent proof replay."""
import argparse
import subprocess
import sys
import time
import tempfile
from pathlib import Path
import test_ff_boolean_proof as suite


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
    sys.argv.extend(['--backend', 'native', '--boolean-backend', 'incremental'])
    suite.main()
