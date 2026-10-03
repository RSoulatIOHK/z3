#!/usr/bin/env python3
"""Default proof-mode field/theory combination and original model validation.

Native C++ tests additionally replay the full proof and each field DAG. This
suite checks the public API without selecting a special tactic or FF option.
"""
from z3 import *
set_option(proof=True)
import test_ff_combination as combination

original_check = combination.check
def has_field_evidence(proof):
    seen, todo = set(), [proof]
    while todo:
        p = todo.pop()
        if p.get_id() in seen: continue
        seen.add(p.get_id())
        if not is_app(p): continue
        if p.decl().kind() == Z3_OP_PR_TH_LEMMA:
            params = p.decl().params()
            if len(params) == 3 and params[:2] == ['ff', 'pac']:
                assert str(params[2].decl().name()) == 'ff-pac'
                return True
        todo.extend(p.children())
    return False


counts = {'unsat': 0, 'field': 0, 'sat': 0}


def checked(factory, constraints, expected, label):
    solver = original_check(factory, constraints, expected, label)
    if expected == unsat:
        proof = solver.proof()
        assert is_false(proof.arg(proof.num_args() - 1)), (label, proof)
        counts['unsat'] += 1
        counts['field'] += has_field_evidence(proof)
    else:
        counts['sat'] += 1
    return solver


combination.check = checked
combination.examples(lambda: Solver())  # Includes arrays, sequences and datatypes.
assert counts['field'] > 0 and counts['sat'] > 0
print('FF_NATIVE_PROOF_PASS', counts)
