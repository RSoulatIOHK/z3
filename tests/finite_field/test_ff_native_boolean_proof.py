"""Exercise native CDCL evidence through the independent Boolean proof oracles."""
import sys
import time
import test_ff_boolean_proof as suite

if __name__ == '__main__':
    original_run = suite.pp.run
    bad = [
        '(ff-boolean-result :status sat :variables (b1) :model (false) :clauses ())',
        '(ff-boolean-result :status unsat :variables (b1) :model () :clauses ((-1)))',
        '(ff-boolean-result :status unsat :variables (b1) :model () :clauses (()))',
        '(ff-boolean-result :status unsat :variables (b2) :model () :clauses (()))',
        '(ff-boolean-result :status unsat :variables (b1) :model () :clauses ((2)))',
        '(ff-boolean-result :status unknown :variables (b1) :model () :clauses ())',
    ]
    try:
        for text in bad:
            suite.pp.run = lambda *a, **kw: {'stdout': text}
            suite.reject(lambda: suite.bp.NativeSearch([(1,)], 'unused', time.monotonic() + 10).search())
    finally:
        suite.pp.run = original_run
    print(f'{len(bad)} corrupt native SAT responses rejected')
    sys.argv.extend(['--backend', 'native'])
    suite.main()
