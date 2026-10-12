#!/usr/bin/env python3
"""Independent finite checks for the submitted Howroyd argument.

Does not import the submitted verifier. Uses only the Python standard library.
The graph is constructed from L1-distance-2 moves. Its triangles are found as
3-cliques by intersections of neighbor sets (not by the submitted incidence
routine). Full-graph maximum-independent-set counts use row dynamic programming
and a max/count subset transform, not the claimed bulk/corner classification.
These finite checks do not replace the all-degree arguments.

Usage:
  python referee_checks.py structural --csv submission/howroyd_cover_weights.csv
  python referee_checks.py dp --max-degree 20
"""
from __future__ import annotations
import argparse
import csv
import json
from collections import Counter
from itertools import combinations, product
from pathlib import Path
import time

Vertex = tuple[int, int, int]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def vertices(d: int) -> list[Vertex]:
    return [(x,y,d-x-y) for x in range(d+1) for y in range(d-x+1)]


def l1(u: Vertex, v: Vertex) -> int:
    return sum(abs(a-b) for a,b in zip(u,v))


def reduced(t: int) -> int:
    require(t >= 0, 'Negative coordinate')
    while t > 6:
        t -= 3
    return t


def graph(d: int):
    vs=vertices(d)
    neighbors={v:set() for v in vs}
    for v in vs:
        for i in range(3):
            if v[i]==0:
                continue
            for j in range(3):
                if i==j:
                    continue
                u=list(v); u[i]-=1; u[j]+=1
                neighbors[v].add(tuple(u))
    return vs,neighbors


def triangles_from_graph(neighbors):
    for a in neighbors:
        for b in neighbors[a]:
            if a >= b:
                continue
            for c in neighbors[a] & neighbors[b]:
                if b < c:
                    yield (a,b,c)


def load_table(path: Path):
    weights={}
    with path.open(newline='') as f:
        for row in csv.DictReader(f):
            key=(int(row['degree_mod_3']),row['type'],int(row['a']),int(row['b']),int(row['c']))
            require(key not in weights,'Duplicate key')
            w=int(row['weight_numerator_over_60'])
            require(w>=0,'Negative weight')
            weights[key]=w
    require(len(weights)==89,'Wrong key count')
    return weights


def triangle_key(d: int, tri):
    base=tuple(min(v[i] for v in tri) for i in range(3))
    deficit=d-sum(base)
    require(deficit in (1,2),f'Unexpected triangle shape: {tri}')
    kind='U' if deficit==1 else 'D'
    return (d%3,kind,*sorted(reduced(t) for t in base))


def local_enumeration():
    # Test ALL 2^10 subsets, without prefiltering the vertex set.
    local=[(p,q) for p in range(4) for q in range(4-p)]
    embed=lambda v:(10-v[0]-v[1],v[0],v[1])
    shell=[(p,4-p) for p in range(5)]
    answer={}
    for delta in range(3):
        fixed=[v for v in shell if (v[0]-v[1])%3==delta]
        allowed=[v for v in local if all(l1(embed(v),embed(u))!=2 for u in fixed)]
        best=-1; solutions=[]
        for mask in range(1<<10):
            chosen=[local[i] for i in range(10) if mask>>i&1]
            if any(l1(embed(u),embed(v))==2 for u,v in combinations(chosen,2)):
                continue
            if any(l1(embed(u),embed(v))==2 for u in chosen for v in fixed):
                continue
            if len(chosen)>best:
                best=len(chosen); solutions=[chosen]
            elif len(chosen)==best:
                solutions.append(chosen)
        expected=(4,1) if delta==0 else (3,3)
        require((best,len(solutions))==expected,'Local count mismatch')
        answer[delta]={'allowed':len(allowed),'maximum':best,'solutions':solutions}
    return answer


def structural_checks(path: Path, max_degree: int):
    weights=load_table(path)
    forbidden={'U':{(0,1),(1,1),(1,2)},'D':{(0,0),(0,2),(1,1)}}
    for (r,kind,a,b,c),w in weights.items():
        require((w==0)==((a,b) in forbidden[kind] and c>=4),'Bad zero support')
    counts=Counter(); by_degree=[]; base_keys=set(); global_checks=[]
    for d in range(10,max_degree+1):
        if d%3==0:
            continue
        vs,ng=graph(d)
        # Independent direct all-pairs adjacency check on the base degrees.
        if d<=21:
            for u,v in combinations(vs,2):
                require((v in ng[u])==(l1(u,v)==2),'Adjacency mismatch')
        coverage=Counter({v:0 for v in vs}); positive=[]; total=0
        for tri in triangles_from_graph(ng):
            require(all(l1(u,v)==2 for u,v in combinations(tri,2)),'Not a clique')
            key=triangle_key(d,tri)
            require(key in weights,'Missing triangle key')
            w=weights[key]
            for v in tri:
                coverage[v]+=w
            if w>0:
                positive.append(tri)
            total+=1
            if d<=21:
                base_keys.add(key)
        require(total==d*d,f'Wrong number of triangles at {d}')
        require(set(coverage.values())=={60},f'Bad coverage at {d}')
        counts['vertex_equations']+=len(vs)
        counts['triangles']+=total
        if d<=21:
            counts['base_vertex_equations']+=len(vs)
            counts['base_triangles']+=total
        # Positive shared-edge equations induce equality of the third vertices.
        body={v for v in vs if max(v)<=d-4}
        parent={v:v for v in body}
        def root(v):
            while parent[v]!=v:
                parent[v]=parent[parent[v]]; v=parent[v]
            return v
        def unite(u,v):
            parent[root(u)]=root(v)
        across={}
        for tri in positive:
            for omitted in range(3):
                third=tri[omitted]
                edge=tuple(tri[i] for i in range(3) if i!=omitted)
                if edge in across:
                    other=across[edge]
                    if third in body and other in body:
                        require((third[0]-third[1]-other[0]+other[1])%3==0,'Equality edge changes color')
                        unite(third,other)
                else:
                    across[edge]=third
        comps={root(v) for v in body}
        require(len(comps)==3,f'Wrong body-component count at {d}')
        color_roots={j:{root(v) for v in body if (v[0]-v[1])%3==j} for j in range(3)}
        require(all(len(s)==1 for s in color_roots.values()),'Body color disconnected')
        # Check ALL maximizers in a tie, not only one predetermined coordinate.
        for v in body:
            for i in range(3):
                if v[i]!=max(v):
                    continue
                u=tuple(v[j]+1-3*(i==j) for j in range(3))
                require(u in body,'Max-coordinate move exits body')
                shared=[tuple(v[t]-(t==i)+(t==j) for t in range(3)) for j in range(3) if j!=i]
                for tri in (tuple([v]+shared),tuple([u]+shared)):
                    require(weights[triangle_key(d,tri)]>0,'Nonpositive balancing triangle')
                counts['all_tied_maximum_moves']+=1
        by_degree.append({'d':d,'vertices':len(vs),'triangles':total,'bulk_components':len(comps)})
        # Construct every corner extension using actual 3D colors and body.
        # This is a finite diagnostic, not the independent full-graph DP.
        if d<=32:
            all_sets=set()
            for j in range(3):
                fixed={v for v in body if (v[0]-v[1])%3==j}
                choices=[]
                for i in range(3):
                    corner=[v for v in vs if v[i]>=d-3]
                    require(len(corner)==10,'Corner size mismatch')
                    best=-1; opt=[]
                    for mask in range(1<<10):
                        I=frozenset(corner[t] for t in range(10) if mask>>t&1)
                        if any((ng[v]&I) or (ng[v]&fixed) for v in I):
                            continue
                        if len(I)>best:
                            best=len(I);opt=[I]
                        elif len(I)==best:
                            opt.append(I)
                    choices.append(opt)
                require(sorted(len(c) for c in choices)==[1,3,3],'Corner extension count')
                for parts in product(*choices):
                    I=frozenset(fixed).union(*parts)
                    require(len(I)*3==len(vs),'Wrong global construction size')
                    require(not any(ng[v]&I for v in I),'Global construction is not independent')
                    all_sets.add(I)
            require(len(all_sets)==27,'Global construction duplicate/count error')
            global_checks.append({'d':d,'size':len(vs)//3,'distinct_constructions':len(all_sets)})
    require(base_keys==set(weights),'Certificate key coverage mismatch')
    require(counts['base_vertex_equations']==1134,'Base count mismatch')
    return {'weight_keys':len(weights),'positive_keys':sum(w>0 for w in weights.values()),
            'zero_keys':sum(w==0 for w in weights.values()),'degrees':by_degree,
            'counts':dict(counts),'corners':local_enumeration(),
            'global_constructions':global_checks}


def independent_masks(length: int):
    # Recursive generation of binary strings with no two adjacent ones.
    def rec(pos: int, mask: int):
        if pos>=length:
            yield mask
            return
        yield from rec(pos+1,mask)
        yield from rec(pos+2,mask|(1<<pos))
    return rec(0,0)


def full_graph_dp(max_degree: int):
    """Counts all maximum sets, with no assumption on alpha, colors or corners.

    A short row mask s and the following longer row mask t are compatible iff
    s & (t | (t >> 1)) == 0. Within a row, adjacent one-bits are prohibited.
    The subset transform finds the maximum size and number of compatible
    previous configurations. Every complete set has a unique row decomposition.
    Python integers keep counts exact and unbounded.
    """
    best=[0]; ways=[1]; result=[]
    for length in range(1,max_degree+2):
        n=length-1
        sb=best[:]; sw=ways[:]
        for bit in range(n):
            h=1<<bit
            for start in range(0,1<<n,h<<1):
                end=start+h
                for lo in range(start,end):
                    hi=lo+h
                    if sb[lo]>sb[hi]:
                        sb[hi]=sb[lo];sw[hi]=sw[lo]
                    elif sb[lo]==sb[hi]:
                        sw[hi]+=sw[lo]
        best=[-10**9]*(1<<length);ways=[0]*(1<<length)
        full=(1<<n)-1
        for t in independent_masks(length):
            allowed=full & ~(t | (t>>1))
            best[t]=t.bit_count()+sb[allowed]
            ways[t]=sw[allowed]
        optimum=max(best)
        count=sum(c for b,c in zip(best,ways) if b==optimum)
        result.append({'d':length-1,'alpha':optimum,'maximum_independent_sets':count})
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode',choices=['structural','dp'])
    parser.add_argument('--csv',type=Path,default=Path(__file__).parent/'submission/howroyd_cover_weights.csv')
    parser.add_argument('--max-degree',type=int)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    start=time.monotonic()
    n=args.max_degree if args.max_degree is not None else (60 if args.mode=='structural' else 20)
    require(n>=0,'Negative maximum degree')
    result=structural_checks(args.csv,n) if args.mode=='structural' else full_graph_dp(n)
    data={'mode':args.mode,'max_degree':n,'elapsed_seconds':time.monotonic()-start,'result':result}
    text=json.dumps(data,indent=2)
    if args.output:
        args.output.write_text(text+'\n')
    print(text)

if __name__=='__main__':
    main()
