"""Compound gate certificates with split wires, signed intermediates and SAT controls."""
import argparse
import copy
import json
from pathlib import Path
import sys
import tempfile

ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'scripts'))
import ff_boolean_proof as bp
import ff_circuit_proof as cp
import ff_proof_pipeline as pp
from test_ff_range_proof import circuit,LARGE
from test_ff_boolean_proof import evaluate,reject


def mux(p,reverse=False):
    text=circuit(4,p,reverse=reverse)
    z,o=f'#f0m{p}',f'#f1m{p}'
    text=text.replace('(declare-const y F)','(declare-const h F)\n(declare-const m F)\n(declare-const y F)')
    total='(ff.add f3 f2 f1 f0)' if reverse else '(ff.add f0 f1 f2 f3)'
    text=text.replace(total,'(ff.add h f3)').replace('(or x0 x1 x2 x3)','(or (ite x2 x0 x1) x3)')
    text=text.replace('(and (= ',f'(and (= m (ff.mul f2 (ff.add f0 (ff.neg f1)))) (= h (ff.add f1 m)) (= ',1)
    return text


def xor(p):
    text=circuit(3,p)
    text=text.replace('(declare-const y F)','(declare-const h F)\n(declare-const m F)\n(declare-const y F)')
    text=text.replace('(ff.add f0 f1 f2)','(ff.add h f2)').replace('(or x0 x1 x2)','(or (xor x0 x1) x2)')
    text=text.replace('(and (= ',f'(and (= m (ff.mul #f2m{p} f0 f1)) (= h (ff.add f0 f1 (ff.neg m))) (= ',1)
    return text


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    for n in ['z3','carcara','ffpacheck']:ap.add_argument('--'+n,required=True)
    args=ap.parse_args();count=0
    # A shared sum DAG has exponentially many tree occurrences. Matching must
    # memoize it, or decline it, rather than recursively unfold all occurrences.
    text=f'(set-logic QF_FF) (declare-const x (_ FiniteField {LARGE}))\n'
    text+=f'(define-fun t0 () (_ FiniteField {LARGE}) x)\n'
    for i in range(1,61):text+=f'(define-fun t{i} () (_ FiniteField {LARGE}) (ff.add t{i-1} t{i-1}))\n'
    text+='(assert (= t60 t60))'
    graph=bp.Graph(text);x=graph.names['x'];target=graph.names['t60']
    forbidden=lambda *args: (_ for _ in ()).throw(AssertionError('unexpected gate for an unsupported coefficient'))
    assert cp.regroup(graph,target,{x:0},[],graph.node,forbidden,forbidden,forbidden,forbidden) is None

    with tempfile.TemporaryDirectory(prefix='ff-circuit-tests-') as temp:
        for p in (7,LARGE):
            for text in (mux(p),mux(p,True),xor(p)):
                proof=bp.produce(text,args.z3,10,backend='native',boolean_backend='circuits')
                files=bp.verify_export(text,proof);d=Path(temp)/str(count);d.mkdir()
                (d/'problem.smt2').write_text(text);(d/'boolean-certificate.json').write_text(json.dumps(proof))
                for n,v in files.items():(d/n).write_text(v)
                bp.check_bundle(d,args.carcara,args.ffpacheck,10);count+=1
                assert proof['version']==4
                bad=copy.deepcopy(proof);bad['version']=3
                reject(lambda:bp.verify_export(text,bad))
                bad=copy.deepcopy(proof);field=next(r for r in bad['records'] if r['rule']=='field');field['literals'].pop()
                reject(lambda:bp.verify_export(text,bad))
        # Replacing subtraction by addition invalidates the mux law. Its signed
        # wire can no longer be folded into a bit merely because it looks similar.
        text=mux(7).replace('(ff.add f0 (ff.neg f1))','(ff.add f0 f1)')
        assignment=dict(x0=False,x1=True,x2=True,x3=False,f0=0,f1=1,f2=1,f3=0,m=1,h=2,y=1,w=4)
        assert evaluate(bp.Graph(text),assignment)
        assert pp.run([args.z3,'-in'],5,text+'(check-sat)\n')['stdout'].strip()=='sat'
        reject(lambda:bp.produce(text,args.z3,1,backend='native',boolean_backend='circuits'))
    print(f'compound circuit proofs: {count} externally checked; signed-wire SAT witness and certificate corruptions rejected')


if __name__=='__main__':main()
