"""Exercise the shared native elimination path with independent certificate oracles."""
import argparse
import subprocess
import test_ff_certificates as suite

_original_run = suite.run

def native_run(binary, text, options=''):
    return _original_run(binary, text, ':backend native ' + options)

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--z3', required=True)
    args = parser.parse_args()
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
            result = subprocess.run([args.z3] + ['smt.ff.' + option for option in variant] + ['-in'],
                                    input=text + '(ff-certify :backend native)\n',
                                    text=True, capture_output=True, timeout=15)
            assert result.returncode == 0 and not result.stderr, result
            suite.check_both(text, result.stdout)
    print(f'{len(variants)*4} native scalar/matrix/storage variants independently checked')
    suite.run = native_run
    suite.main()
