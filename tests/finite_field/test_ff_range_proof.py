"""Certified symbolic circuit ranges, modular-wrap controls and corruptions."""
import argparse
import copy
import json
from pathlib import Path
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT/'scripts'))
import ff_boolean_proof as bp
import ff_proof_pipeline as pp
from test_ff_boolean_proof import evaluate, reject

LARGE = 52435875175126190479447740508185965837690552500527637822603658699938581184513


def circuit(n, p, reverse=False, complemented=False, prefix='x', optional=False):
    """Fresh OR circuits, independent of the artifact's generated names/layout."""
    names = [f'{prefix}{i}' for i in range(n)]
    z,o = f'#f0m{p}',f'#f1m{p}'
    lines = [f'(set-logic QF_FF)', f'(define-sort F () (_ FiniteField {p}))']
    lines += [f'(declare-const {v} Bool)' for v in names]
    lines += [f'(declare-const f{i} F)' for i in range(n)]
    lines += ['(declare-const y F)','(declare-const w F)']
    links = [f'(= f{i} (ite {v} {o} {z}))' for i,v in enumerate(names)]
    terms = [f'f{i}' for i in range(n)]
    if reverse: terms.reverse(); links.reverse()
    total = '(ff.add '+' '.join(terms)+')'
    value = f'(ff.add {o} (ff.neg y))' if complemented else 'y'
    opposite = 'y' if complemented else f'(ff.add {o} (ff.neg y))'
    constraints = links+[f'(= (ff.mul w {total}) {value})', f'(= (ff.mul {opposite} {total}) {z})']
    prop = f'(and (or (= {value} {z}) (= {value} {o})) (= (= {value} {o}) (or {" ".join(names)})))'
    premise = '(and '+' '.join(constraints)+')'
    if optional: premise = f'(or true {premise})'
    lines.append(f'(assert (not (=> {premise} {prop})))')
    return '\n'.join(lines)+'\n'


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    for name in ['z3','carcara','ffpacheck']: ap.add_argument('--'+name,required=True)
    args=ap.parse_args();checked=0
    with tempfile.TemporaryDirectory(prefix='ff-range-tests-') as temp:
        root=Path(temp)
        def certify(text):
            nonlocal checked
            proof=bp.produce(text,args.z3,10,backend='native',boolean_backend='ranges')
            files=bp.verify_export(text,proof)
            d=root/str(checked);d.mkdir();(d/'problem.smt2').write_text(text)
            (d/'boolean-certificate.json').write_text(json.dumps(proof))
            for name,value in files.items(): (d/name).write_text(value)
            bp.check_bundle(d,args.carcara,args.ffpacheck,10);checked+=1
            return proof,d
        for p,n in [(7,2),(7,3),(LARGE,10)]:
            for reverse,complement in [(False,False),(True,True)]:
                text=circuit(n,p,reverse,complement,prefix='renamed_')
                proof,d=certify(text)
                bad=copy.deepcopy(proof)
                field=next(r for r in bad['records'] if r['rule']=='field')
                field['literals']=field['literals'][:-1]
                reject(lambda: bp.verify_export(text,bad))
                # Cross-input reuse must fail independent original-input binding.
                reject(lambda: bp.verify_export(text.replace('(or renamed_', '(and renamed_',1),proof))
        # Compose AND, NOT and OR without depending on names or clause order.
        text=circuit(3,7)
        text=text.replace('(declare-const y F)', '(declare-const h F)\n(declare-const y F)')
        text=text.replace('(ff.add f0 f1 f2)', '(ff.add h f2)')
        text=text.replace('(or x0 x1 x2)', '(or (and x0 (not x1)) x2)')
        text=text.replace('(and (= f0', '(and (= h (ff.mul f0 (ff.add #f1m7 (ff.neg f1)))) (= f0')
        certify(text)
        # A prime-field sum wraps at p: OR is then not represented by nonzero.
        # Explicit satisfying assignments are checked by an independent evaluator.
        for p in (2,3):
            text=circuit(p,p);g=bp.Graph(text)
            assignment={f'x{i}':True for i in range(p)}
            assignment.update({f'f{i}':1 for i in range(p)});assignment.update(y=0,w=0)
            assert evaluate(g,assignment)
            assert pp.run([args.z3,'-in'],5,text+'(check-sat)\n')['stdout'].strip()=='sat'
            reject(lambda: bp.produce(text,args.z3,1,backend='native',boolean_backend='ranges'))
        # Matching equations in a disjunction never authorizes asserting them.
        text=circuit(2,7,optional=True);g=bp.Graph(text)
        assignment=dict(x0=True,x1=False,f0=1,f1=0,y=0,w=0)
        assert evaluate(g,assignment)
        reject(lambda: bp.produce(text,args.z3,1,backend='native',boolean_backend='ranges'))
        # All cut units must be literal definitional equalities accepted by refl.
        text=circuit(3,7);g=bp.Graph(text,True);base=bp.Clauses(g)
        assert g.cut_definitions
        for c,source in zip(base.clauses,base.sources):
            if source[0]=='cut':
                a,b=g.nodes[c[0]][1];assert g.cut_definitions[a]==b
        proof,d=certify(text)
        data=(d/'proof.alethe').read_text();assert ':rule refl)' in data
        (d/'proof.alethe').write_text(data.replace(':rule refl)',':rule hole)',1))
        reject(lambda: bp.check_bundle(d,args.carcara,args.ffpacheck,10))
        # No relevant bit/zero-test syntax: ordinary integrated refutation works.
        certify('(set-logic QF_FF) (declare-const a Bool) (assert (and a (not a)))')
    print(f'range lemmas: {checked} externally checked circuits; modular-wrap, conditional-premise and corruption controls passed')


if __name__=='__main__': main()
