#!/usr/bin/env python3
"""Summarize a paired proof-backend screen without mixing solver and proof success."""
import argparse
from collections import Counter
import json
from pathlib import Path
import statistics


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory', type=Path)
    args = parser.parse_args()
    out = args.directory
    meta = json.loads((out / 'metadata.json').read_text())
    rows = [json.loads(x) for x in (out / 'runs.jsonl').read_text().splitlines()]
    selection = json.loads((out / 'selection.json').read_text())
    weights = Counter(r['sha256'] for r in selection)
    by = {c['id']: {} for c in meta['configurations']}
    for r in rows:
        assert r['sha256'] not in by[r['configuration']], 'duplicate measurement'
        by[r['configuration']][r['sha256']] = r
    assert all(set(rs) == set(weights) for rs in by.values()), 'incomplete paired corpus'
    summary = {'distinct': len(weights), 'members': len(selection), 'configurations': {}, 'pairs': {}}
    for name, rs in by.items():
        successes = [r for r in rs.values() if r['status'] == 'checked']
        summary['configurations'][name] = {
            'statuses': dict(Counter(r['status'] for r in rs.values())),
            'checked': len(successes),
            'weighted_checked': sum(weights[r['sha256']] for r in successes),
            'produced': sum(bool(r.get('produced')) for r in rs.values()),
            'median_seconds': statistics.median(r['seconds'] for r in successes) if successes else None,
        }
    # Paired timings exclude inputs checked by just one side, including gains.
    for left, right in [('base-proof', 'new-auto-proof'), ('base-proof', 'new-f4-proof'),
                        ('paper-candidate-proof', 'new-auto-proof')]:
        if left not in by or right not in by: continue
        a, b = by[left], by[right]
        sa = {h for h, r in a.items() if r['status'] == 'checked'}
        sb = {h for h, r in b.items() if r['status'] == 'checked'}
        common = sorted(sa & sb)
        summary['pairs'][left + ' -> ' + right] = {
            'common': len(common),
            'gains': [dict(sha256=h, member=b[h]['member']) for h in sorted(sb-sa)],
            'losses': [dict(sha256=h, member=a[h]['member']) for h in sorted(sa-sb)],
            'common_seconds': {left: sum(a[h]['seconds'] for h in common),
                               right: sum(b[h]['seconds'] for h in common)},
            'median_ratio': statistics.median(b[h]['seconds']/a[h]['seconds'] for h in common) if common else None,
        }
    (out / 'summary.json').write_text(json.dumps(summary, indent=2)+'\n')
    table = ['| Configuration | Checked / '+str(len(weights))+' | Weighted / '+str(len(selection))+' | Median |',
             '|---|---:|---:|---:|']
    for name, r in summary['configurations'].items():
        median = f"{r['median_seconds']:.3f} s" if r['median_seconds'] is not None else '—'
        table.append(f"| {name} | {r['checked']} | {r['weighted_checked']} | {median} |")
    (out / 'table.md').write_text('\n'.join(table)+'\n')
    print('\n'.join(table))


if __name__ == '__main__':
    main()
