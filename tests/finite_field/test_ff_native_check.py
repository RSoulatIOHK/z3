#!/usr/bin/env python3
"""Input-bound native proof replay: explicit supported profile, no fallback."""
import argparse
import re
import subprocess

parser = argparse.ArgumentParser()
parser.add_argument('--z3', required=True)
args = parser.parse_args()
marker = re.compile(r'^\(ff-native-proof-checked :field-lemmas (\d+)\)$', re.M)
pre = '(set-option :produce-proofs true)\n(set-logic QF_FF)\n(declare-const x (_ FiniteField 7))\n'
root = '(assert (= (ff.mul x x) #f3m7))\n'
check = '(check-sat)\n(ff-check-native-proof)\n'


def run(text, expected=0, error=None, field=False):
    p = subprocess.run([args.z3, '-in'], input=text, text=True, capture_output=True, timeout=20)
    matches = marker.findall(p.stdout)
    assert len(matches) == expected, (text, p.returncode, p.stdout, p.stderr)
    if error:
        assert error in p.stdout + p.stderr and p.returncode != 0, (p.stdout, p.stderr)
    else:
        assert p.returncode == 0 and '(error' not in p.stdout + p.stderr, (p.stdout, p.stderr)
    if field: assert any(int(n) > 0 for n in matches), p.stdout


run(pre + root + check, 1, field=True)
# Reversed wire definitions must be justified through preprocessing.
run(pre + '(declare-const y (_ FiniteField 7))\n(assert (= (ff.add x #f1m7) y))\n'
    '(assert (= (ff.mul y y) #f3m7))\n' + check, 1, field=True)
# Boolean composition and scope restoration remain bound to current input.
run(pre + '(declare-const b Bool)\n(assert (or b (= (ff.mul x x) #f3m7)))\n'
    '(assert (not b))\n' + check, 1, field=True)
run(pre + '(declare-const a Bool) (declare-const b Bool)\n'
    '(assert (= a (not b)))\n(assert (= b a))\n' + check, 1)
run(pre + '(assert (or (= x #f0m7) (= x #f1m7)))\n'
    '(assert (not (= x #f1m7)))\n(assert (not (= x #f0m7)))\n' + check, 1)
run(pre + '(push)\n' + root + check + '(pop)\n(assert (= x #f0m7))\n'
    '(push)\n(assert (= x #f1m7))\n' + check + '(pop)\n(check-sat)\n', 2)
run('(set-logic QF_FF)\n(declare-const x (_ FiniteField 7))\n' + root + check,
    error='an UNSAT result with native proofs is required')
run(pre + check, error='an UNSAT result with native proofs is required')
run(pre + '(ff-check-native-proof)\n', error='an UNSAT result with native proofs is required')
# Assumptions are not silently promoted to original assertions.
run(pre + '(check-sat-assuming ((= (ff.mul x x) #f3m7)))\n(ff-check-native-proof)\n',
    error='native proof assertion is absent from the original input')
# Unsupported source theories are rejected even when an FF subset refutes it.
for extra in ['(declare-const n Int) (assert (= n 0))',
              '(declare-fun f ((_ FiniteField 7)) (_ FiniteField 7)) (assert (= (f x) x))',
              '(declare-const a (Array Bool (_ FiniteField 7))) (assert (= (select a true) x))']:
    run(pre.replace('QF_FF', 'ALL') + extra + '\n' + root + check,
        error='native proof checker profile requires pure ground QF_FF')
print('NATIVE_FF_CHECK_PASS')
