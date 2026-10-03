#!/usr/bin/env python3
"""Failure-path checks for the acceptance runner; no Z3 build is required."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from run_tests import execute

RUNNER = Path(__file__).with_name('run_tests.py')


@unittest.skipUnless(os.name == 'posix', 'runner supports Linux/macOS')
class RunnerTests(unittest.TestCase):
    def test_nonzero_exit_and_diagnostic_are_preserved(self):
        with tempfile.TemporaryDirectory() as temp:
            out = Path(temp)
            result = execute('failure', [sys.executable, '-c',
                             'import sys; print("intentional failure"); sys.exit(7)'],
                             dict(os.environ), out, 10)
            self.assertEqual(result['status'], 'failed')
            self.assertEqual(result['returncode'], 7)
            self.assertIn('intentional failure', (out / 'failure.log').read_text())

    def test_native_zero_exit_requires_completion(self):
        for message in ['', 'did not verify: l_true', 'PASS',
                        'PASS\n(test wrong_test :time 0.0)']:
            with self.subTest(message=message), tempfile.TemporaryDirectory() as temp:
                result = execute('native-smt_proof_checker',
                                 [sys.executable, '-c', 'print(' + repr(message) + ')'],
                                 dict(os.environ), Path(temp), 10)
                self.assertEqual(result['status'], 'failed')
                self.assertEqual(result['returncode'], 0)

    def test_native_completed_negative_tests_are_allowed(self):
        # Tests deliberately exercising rejected proofs may print diagnostics;
        # only reaching their final completion marker demonstrates success.
        with tempfile.TemporaryDirectory() as temp:
            message = 'did not verify: l_true\nPASS\n(test smt_proof_checker :time 0.0)'
            result = execute('native-smt_proof_checker',
                             [sys.executable, '-c', 'print(' + repr(message) + ')'],
                             dict(os.environ), Path(temp), 10)
            self.assertEqual(result['status'], 'passed')

    def test_timeout_is_failure(self):
        with tempfile.TemporaryDirectory() as temp:
            result = execute('timeout', [sys.executable, '-c', 'import time; time.sleep(60)'],
                             dict(os.environ), Path(temp), 0.1)
            self.assertEqual(result['status'], 'timeout')
            self.assertLess(result['seconds'], 10)

    def test_wrong_build_fails_before_running_suites(self):
        with tempfile.TemporaryDirectory() as temp:
            out = Path(temp) / 'logs'
            result = subprocess.run([sys.executable, str(RUNNER), '--build', temp,
                                     '--out', str(out)], capture_output=True, text=True, timeout=20)
            self.assertNotEqual(result.returncode, 0)
            summary = json.loads((out / 'summary.json').read_text())
            self.assertEqual(len(summary['results']), 1)
            self.assertEqual(summary['results'][0]['status'], 'failed')

    def test_missing_checkers_cannot_silently_pass(self):
        with tempfile.TemporaryDirectory() as temp:
            result = subprocess.run([sys.executable, str(RUNNER), '--build', temp,
                                     '--out', str(Path(temp) / 'logs'), '--suite', 'proofs'],
                                    capture_output=True, text=True, timeout=10)
            self.assertEqual(result.returncode, 2)
            self.assertIn('require --carcara and --ffpacheck', result.stderr)


if __name__ == '__main__':
    unittest.main()
