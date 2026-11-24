#!/usr/bin/env python3
"""Exact scalar-antighost transcription of the submitted Wick recursion.

Uses fractions, labelled legs and each parent/child scale inequality. This is
an independent executable audit of Glue.bridgeG/innerTrace and Ordered.factor,
not an execution of Lean Mob functions or a formal equivalence theorem.
"""
import argparse, hashlib, json
from pathlib import Path
from datetime import datetime, timezone
from fractions import Fraction as Q
from itertools import combinations, permutations, product
from collections import defaultdict, Counter
from functools import lru_cache

@lru_cache(None)
def shapes(n):
    if n == 1:
        return (None,)
    return tuple((l, r) for k in range(1,n) for l in shapes(k) for r in shapes(n-k))

def size(t):
    return 1 if t is None else size(t[0])+size(t[1])

def odd(f): return f[0] != 'A'

def splits(w, count):
    for ix in combinations(range(len(w)),count):
        chosen=set(ix)
        l=tuple(w[i] for i in ix)
        r=tuple(f for i,f in enumerate(w) if i not in chosen)
        exponent=sum(odd(w[i])*odd(w[j]) for i in range(len(w)) for j in ix if i<j and i not in chosen)
        yield l,r,(-1)**exponent

def vertex(w):
    if sorted(f[0] for f in w)!=['A','b','c']: return []
    a=next(f[1] for f in w if f[0]=='A')
    sign=1 if next(i for i,f in enumerate(w) if f[0]=='b') < next(i for i,f in enumerate(w) if f[0]=='c') else -1
    return [(Q(sign),tuple((f,a) for f in w if odd(f)))]

@lru_cache(None)
def tree(t,w,path):
    if len(w)!=size(t)+2: return ()
    if t is None: return tuple(vertex(w))
    terms=[]
    # bridgeG: factor true (1/2) times 2*K; K has the Wick half.
    for l,r,shuffle in splits(w,size(t[0])+1):
        for i,j,half in [('c','b',Q(1,2)),('b','c',Q(-1,2))]:
            cross=(-1)**sum(map(odd,l))
            for (a,pa),(b,pb) in product(tree(t[0],((i,path),)+l,path+'L'),tree(t[1],((j,path),)+r,path+'R')):
                terms.append((shuffle*cross*half*a*b,pa+pb))
    return tuple(terms)

def contractions(t,n):
    w=tuple(('A',i) for i in range(n))
    for i,j,half in [('c','b',Q(1,2)),('b','c',Q(-1,2))]:
        for coef,ports in tree(t,((i,'O'),(j,'O'))+w,'T'):
            endpoints=dict(ports)
            edges={edge:(endpoints[('c',edge)],endpoints[('b',edge)]) for kind,edge in endpoints}
            yield coef*half,edges

def canonical(edges,n):
    nxt=dict(edges.values())
    path=[0]
    while nxt[path[-1]] != 0:
        assert nxt[path[-1]] not in path
        path.append(nxt[path[-1]])
    assert len(path)==n
    return tuple(path)

def run(n, omit_shape=None):
    weights=defaultdict(Q)
    raw=Counter()
    terms_per_cell=Counter()
    coefficients=Counter()
    for idx,t in enumerate(shapes(n)):
        if idx == omit_shape: continue
        for coef,edges in contractions(t,n):
            cycle=canonical(edges,n)
            raw[idx]+=1
            coefficients[str(coef)]+=1
            assert coef == Q(-1,2**n)
            for order in permutations(edges):
                positions={e:i for i,e in enumerate(order)}
                if order[-1]!='O': continue
                # A child bridge is integrated only below its parent scale.
                if any(positions[e]>=positions[e[:-1]] for e in edges if len(e)>1): continue
                cell=cycle,tuple(edges[e] for e in order)
                weights[cell] += coef
                terms_per_cell[cell] += 1
    assert len(weights)==len(tuple(permutations(range(1,n))))*len(tuple(permutations(range(n))))
    assert set(weights.values())=={Q(-1)},Counter(weights.values())
    assert set(terms_per_cell.values())=={2**n}
    return {'n':n,'shapes':len(shapes(n)), 'raw_contractions':dict(raw),
            'raw_coefficients':dict(coefficients),'ordered_domain_terms':sum(terms_per_cell.values()),
            'terms_per_cell':2**n,'cycle_order_cells':len(weights),
            'weights':dict(Counter(map(str,weights.values())))}

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--source', type=Path, required=True, help='Submitted lean root')
    args = parser.parse_args()
    rows = [run(n) for n in (2,3,4)]
    rejected = False
    try:
        run(4, omit_shape=2)  # Removing the balanced tree leaves missing cells.
    except AssertionError:
        rejected = True
    assert rejected
    inputs = ['YM/MS/KoszulAllocate.lean', 'YM/MS/ScaleForest/Glue.lean',
              'YM/MS/ScaleForest/Ordered.lean', 'YM/MS/ScaleForest/AllHistories.lean',
              'YM/MS/ScaleForest/Halves.lean', 'YM/MS/ScaleForest/HeatScale.lean']
    result = {'checked_utc': datetime.now(timezone.utc).isoformat(),
        'scope': 'Exact rational scalar-antighost transcription; not a Lean evaluator run or formal source-equivalence proof.',
        'cases': rows, 'negative_control_omitting_balanced_tree_rejected': rejected,
        'source_files': {f:hashlib.sha256((args.source/f).read_bytes()).hexdigest() for f in inputs},
        'box_conclusion': 'Each of six directed cyclic orderings and 24 strict edge-scale orders has total coefficient -1. The four half-line factors, bulk bridge factors and all Koszul signs are included.'}
    output = json.dumps(result,indent=2)+'\n'
    if args.output: args.output.write_text(output)
    print(output,end='')
