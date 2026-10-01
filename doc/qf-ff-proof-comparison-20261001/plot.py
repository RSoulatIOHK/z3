from pathlib import Path
from collections import Counter
import json
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np
r=Path(__file__).parent
rows=[json.loads(s) for s in (r/'measurements.jsonl').read_text().splitlines()]
ids=['published-pr2','cvc5','local-circuits']
labels=['Published PR2 · 1920788dc','cvc5 1.3.4.dev · FMCAD proof candidate','Z3+FF native/circuits · local c305dec74']
colors=['#4878b0','#d68520','#298957']
by={c:[x for x in rows if x['series']==c] for c in ids}
inputs={x['sha256'] for x in by[ids[0]]}
for c in ids:
 assert len(by[c])==390 and {x['sha256'] for x in by[c]}==inputs
 assert all(0<x['seconds']<10 and x.get('produced') for x in by[c] if x['status']=='checked')
 assert all(0<x['generation_seconds']<10 for x in by[c] if x.get('produced'))
summary={c:{'produced':sum(bool(x.get('produced')) for x in by[c]),'checked':sum(x['status']=='checked' for x in by[c]),'statuses':dict(Counter(x['status'] for x in by[c]))} for c in ids}
checked={c:{x['sha256'] for x in by[c] if x['status']=='checked'} for c in ids}
overlap={}
for c in [ids[0],ids[2]]:
 z,v=checked[c],checked['cvc5']
 overlap[c]={'both':len(z&v),'z3_only':len(z-v),'cvc5_only':len(v-z),'neither':len(inputs-z-v)}
summary['overlap']=overlap
plt.rcParams.update({'font.size':11,'axes.spines.top':False,'axes.spines.right':False})
fig,axs=plt.subplots(1,2,figsize=(14,6),sharey=True)
for ax,production in zip(axs,[True,False]):
 for c,label,color in zip(ids,labels,colors):
  times=sorted(x['generation_seconds'] if production else x['seconds'] for x in by[c] if (x.get('produced') if production else x['status']=='checked'))
  ax.step(times,range(1,len(times)+1),where='post',label=f'{label} ({len(times)})',color=color,lw=2.2)
 ax.set(xscale='log',xlim=(.025,10),ylim=(0,400),xlabel='Time through certificate export (s)' if production else 'Whole-pipeline wall time (s)',title='Certificates produced' if production else 'Completed checked certificates')
 ax.grid(alpha=.2);ax.legend(loc='upper left',fontsize=8.8)
axs[0].set_ylabel('Distinct inputs')
fig.suptitle('FMCAD finite-field certificates — production and checking',fontsize=17)
fig.text(.5,.072,'390 distinct inputs / 408 paths · 10 s per pipeline · 4 workers · macOS ARM64 · no Lean',ha='center',fontsize=10)
fig.text(.5,.038,'Published PR2 + cvc5: September 29. Local follow-up: September 30; not yet in PR2. Separate campaigns.',ha='center',fontsize=9)
fig.text(.5,.007,'Carcara + FFPacheck; Z3 additionally binds the original input and independently replays proofs. Checking contracts differ.',ha='center',fontsize=9)
fig.tight_layout(rect=(0,.10,1,.95))
for ext in ['png','pdf','svg']:fig.savefig(r/f'certificate-cactus.{ext}',dpi=170)
plt.close(fig)
# Group by circuit frontend and verification property; exact input identity is shared by all series.
groups=[(f,p) for f in ['circ','zokcirc','zokref'] for p in ['deterministic','sound']]
def group(x):
 return (x['member'].split('-ff-')[1].split('-')[0],x['member'].split('compilation-')[1].split('-')[0])
assert {group(x) for x in rows}==set(groups)
ns=[sum(group(x)==g for x in by[ids[0]]) for g in groups]
counts=np.array([[sum(group(x)==g and x['status']=='checked' for x in by[c]) for c in ids] for g in groups])
percent=100*counts/np.array(ns)[:,None]
fig,(ax,bx)=plt.subplots(2,1,figsize=(12,8),gridspec_kw={'height_ratios':[3.4,1.35]})
im=ax.imshow(percent,vmin=0,vmax=100,cmap='YlGn',aspect='auto')
ax.set_xticks(range(3),['Published PR2\n1920788dc','cvc5 1.3.4.dev\nFMCAD candidate','Local Z3+FF follow-up\nc305dec74 · native/circuits'])
ax.set_yticks(range(6),[f'{f.title()} · {"determinism" if p=="deterministic" else "soundness"} (n={n})' for (f,p),n in zip(groups,ns)])
for i in range(6):
 for j in range(3):
  ax.text(j,i,f'{counts[i,j]} / {ns[i]}  ({percent[i,j]:.0f}%)',ha='center',va='center',color='white' if percent[i,j]>75 else '#203020',fontsize=12,fontweight='bold')
fig.colorbar(im,ax=ax,pad=.02,label='Completed checked certificates (%)')
ax.set_title('Coverage by circuit family and property',pad=14)
parts=['both','z3_only','cvc5_only','neither']; partlabels=['Both checked','Z3 only','cvc5 only','Neither'];partcolors=['#548fb0','#52a574','#e2a343','#c9cdd2']
left=np.zeros(2)
for part,label,color in zip(parts,partlabels,partcolors):
 vals=np.array([overlap[c][part] for c in [ids[0],ids[2]]])
 bx.barh([1,0],vals,left=left,color=color,label=label,height=.52)
 for y,n,l in zip([1,0],vals,left):
  if 0<n<5:bx.annotate(str(n),(l+n/2,y+.24),xytext=(l+n/2,y+.48),ha='center',va='center',fontsize=10,arrowprops={'arrowstyle':'-','color':'#444'})
  elif n:bx.text(l+n/2,y,str(n),ha='center',va='center',fontsize=10)
 left+=vals
bx.set_yticks([1,0],['Published PR2 vs cvc5','Local follow-up vs cvc5']);bx.set(xlim=(0,390),xlabel='Distinct inputs (390 total)')
bx.legend(ncol=4,loc='upper center',bbox_to_anchor=(.5,-.44),frameon=False,fontsize=10)
fig.suptitle('FMCAD finite-field certificates — coverage and overlap',fontsize=17)
fig.text(.5,.049,'10 s whole-pipeline deadline · 4 workers · separate September 29/30 campaigns; same 390 input hashes',ha='center',fontsize=9)
fig.text(.5,.020,'Local c305dec74 is not yet in PR2. Checking contracts differ; no claim of Lean validation.',ha='center',fontsize=9)
fig.tight_layout(rect=(0,.13,1,.95),h_pad=2)
for ext in ['png','pdf','svg']:fig.savefig(r/f'certificate-coverage.{ext}',dpi=170)
plt.close(fig)
summary['groups']=[{'family':g[0],'property':g[1],'total':n,'checked':dict(zip(ids,map(int,cs)))} for g,n,cs in zip(groups,ns,counts)]
(r/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
