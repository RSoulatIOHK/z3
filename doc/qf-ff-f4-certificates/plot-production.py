"""Separate produced certificates from fully checked pipelines; no solver-only rows."""
import json
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
R=Path(__file__).resolve().parent
rows=list(map(json.loads,(R/'measurements.jsonl').read_text().splitlines()))
labels={'base-proof':'Z3+FF · PR1 (scalar)','new-auto-proof':'Z3+FF · PR2 (scalar + F4 fallback)','paper-candidate-proof':'cvc5 1.3.4.dev · FMCAD proof candidate'}
plt.rcParams.update({'font.size':11})
fig,axes=plt.subplots(1,2,figsize=(13.6,5.6),sharey=True)
for ax,produced in zip(axes,[True,False]):
 for c,label in labels.items():
  rr=[r for r in rows if r['configuration']==c and (r.get('produced') if produced else r['status']=='checked')];xs=sorted(r['generation_seconds'] if produced else r['seconds'] for r in rr)
  assert len([r for r in rows if r['configuration']==c])==390
  assert all(t<10 for t in xs)
  ax.step(xs,range(1,len(xs)+1),where='post',label=f'{label} ({len(xs)})',linewidth=2)
 ax.set(xscale='log',xlim=(.02,10),ylim=(0,395),xlabel='Time through proof production (s)' if produced else 'Whole-pipeline wall time (s)',title='Certificates produced' if produced else 'Certificates checked')
 ax.grid(alpha=.22);ax.legend(fontsize=8.3,loc='upper left')
axes[0].set_ylabel('Distinct inputs');fig.suptitle('FMCAD proof comparison · 390 inputs · 10 s total deadline · 4 workers',fontsize=14)
fig.text(.5,.035,'Same completed September 29 campaign · no Lean-SMT · produced does not mean checked',ha='center',fontsize=10)
fig.text(.5,.008,'Checked: Carcara + FFPacheck; Z3 also independently replays and binds original inputs. Checking contracts differ.',ha='center',fontsize=9)
fig.tight_layout(rect=(0,.075,1,.94))
for ext in ['png','pdf']:fig.savefig(R/f'production-and-checking.{ext}',dpi=180)
