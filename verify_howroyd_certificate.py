"""Independent exact checks for the Howroyd proof. Python 3.10+, stdlib only.
This file does not import any search, LP, DP, NumPy, or template-construction code.
The infinite reduction and connectivity arguments are in main.tex.
"""
from pathlib import Path
from itertools import product
from collections import Counter
import csv

DENOMINATOR = 60


def require(condition, message):
    if not condition:
        raise ValueError(message)


def load_weights():
    result = {}
    with Path(__file__).with_name('howroyd_cover_weights.csv').open(newline='') as f:
        for row in csv.DictReader(f):
            key = (int(row['degree_mod_3']),row['type'],int(row['a']),int(row['b']),int(row['c']))
            weight = int(row['weight_numerator_over_60'])
            require(key not in result,'Duplicate key')
            require(key[0] in (1,2) and key[1] in ('U','D'),'Invalid type')
            require(0 <= key[2] <= key[3] <= key[4] <= 6,'Invalid categories')
            require(0 <= weight <= 60,'Invalid nonnegative weight')
            result[key] = weight
    require(len(result)==89,'Expected 89 entries')
    return result


def category(t):
    require(t >= 0,'Negative base coordinate')
    return t if t <= 3 else 4+(t-4)%3


def key_for(d, kind, base):
    return (d%3,kind,*sorted(category(t) for t in base))


def compositions(d):
    for a in range(d+1):
        for b in range(d-a+1):
            yield (a,b,d-a-b)


def incident_keys(d,v):
    for i in range(3):
        if v[i] > 0:
            base = tuple(v[j]-(j==i) for j in range(3))
            yield key_for(d,'U',base)
        if all(v[j] > 0 for j in range(3) if j != i):
            base = tuple(v[j]-(j!=i) for j in range(3))
            yield key_for(d,'D',base)


def check_cover(weights, degrees):
    equations = 0; used = set()
    for d in degrees:
        if d%3 == 0: continue
        for v in compositions(d):
            keys = list(incident_keys(d,v))
            require(all(key in weights for key in keys),f'Missing key at {d,v}')
            require(sum(weights[key] for key in keys)==60,f'Bad cover at {d,v}')
            used.update(keys); equations += 1
    return equations, used


def adjacent_2d(u,v):
    return (u[0]-v[0],u[1]-v[1]) in {(1,0),(-1,0),(0,1),(0,-1),(1,-1),(-1,1)}


def check_corners():
    B = [(i,j) for i in range(4) for j in range(4-i)]
    layer = [(i,4-i) for i in range(5)]
    results = []
    for delta in range(3):
        fixed = [v for v in layer if (v[0]-v[1])%3==delta]
        allowed = [v for v in B if all(not adjacent_2d(v,u) for u in fixed)]
        best = -1; solutions=[]
        for mask in range(1<<len(allowed)):
            I = tuple(v for i,v in enumerate(allowed) if mask>>i&1)
            if any(adjacent_2d(u,v) for p,u in enumerate(I) for v in I[p+1:]): continue
            if len(I)>best:best=len(I);solutions=[I]
            elif len(I)==best:solutions.append(I)
        require((best,len(solutions))==((4,1) if delta==0 else (3,3)),'Corner count failed')
        results.append((delta,best,solutions))
    return results


def check_zero_support(weights):
    forbidden_pairs={'U':{(0,1),(1,1),(1,2)},'D':{(0,0),(0,2),(1,1)}}
    zeros=[]
    for key,w in weights.items():
        r,kind,a,b,c=key
        zero_pattern=(a,b) in forbidden_pairs[kind] and c>=4
        require((w==0)==zero_pattern,f'Unexpected zero support {key,w}')
        if not w:zeros.append(key)
    require(len(zeros)==12,'Unexpected number of zero keys')


def extra_checks(weights):
    # Diagnostic checks beyond the finite certificate. These are not used to
    # replace the universal mathematical arguments in main.tex.
    count,_=check_cover(weights,[31,32,49,50,100,101,202])
    moves=0
    for d in range(10,61):
        if d%3==0:continue
        for v in compositions(d):
            if max(v)>d-4:continue
            i=max(range(3),key=lambda j:v[j])
            b=tuple(v[j]-(j==i) for j in range(3))
            c=tuple(v[j]-2*(j==i) for j in range(3))
            require(weights[key_for(d,'U',b)]>0 and weights[key_for(d,'D',c)]>0,'Balancing edge not positive')
            u=tuple(v[j]+1-3*(j==i) for j in range(3))
            require(min(u)>=0 and max(u)<=d-4,'Balancing left bulk')
            require((u[0]-u[1]-v[0]+v[1])%3==0,'Balancing changed color')
            moves+=1
    return count,moves


def main():
    weights=load_weights()
    count,used=check_cover(weights,range(10,22))
    require(count==1134,'Wrong number of base equations')
    require(used==set(weights),'Unused or missing certificate entry')
    check_zero_support(weights)
    print(f'PASS: {len(weights)} nonnegative rational weights, denominator 60; {count} exact vertex-cover equations.')
    print('PASS: zero-support characterization used by the balancing lemma.')
    for delta,best,solutions in check_corners():
        print(f'Corner relative color {delta}: maximum {best}, {len(solutions)} possibilities: {solutions}')
    count,moves=extra_checks(weights)
    print(f'PASS: additional {count} vertex equations and {moves} bulk balancing moves.')
    print('The all-degree conclusion additionally uses the coordinate-reduction and balancing proofs in main.tex.')


if __name__=='__main__':
    main()
