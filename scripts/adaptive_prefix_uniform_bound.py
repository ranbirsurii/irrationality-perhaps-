"""Check a uniform subunit cost certificate, not exponential decay."""
from fractions import Fraction as Q
from pathlib import Path
from math import log
import json
import sys
from signed_prefix_metric import construct


def quadratic(gram,u,v):
    A,B,C=map(Q,gram)
    return A*u*u+2*B*u*v+C*v*v


def main():
    sys.set_int_max_str_digits(200000)
    root=Path(__file__).resolve().parents[1]
    cases=json.loads((root/'notes/signed-prefix-metric.json').read_text())['cases']
    selected=[]
    indices={(x['weight'],x['index']) for x in cases}|{(13,12),(15,14),(17,16),(21,20)}
    for s,n in sorted(indices):
        B=Q(3,2)*Q(2,3)**s; delta=B*B/16; bound=2*B*B
        assert 0<B<1 and bound<Q(1,64)
        seed_pairs=((1,-1),(2**s,-2**s-1))
        candidates=[]
        multiple=Q(2)
        for attempt in range(10):
            stored=[x for x in cases if (x['weight'],x['index'],x['cutoff_multiple'])==(s,n,str(multiple))]
            row=stored[0] if stored else construct((s-1)//2,n,multiple)
            P,T,mu=map(Q,(row['prefix_mass'],row['tail_mass'],row['kernel_mass_majorant']))
            assert mu==P+T and P>0 and T>0
            energies=[quadratic(row['raw_tail_gram'],u,v) for u,v in seed_pairs]
            assert min(energies)>0
            if T/P>delta or mu*max(energies)>delta**2:
                multiple*=2
                continue
            certificates=[mu*quadratic(row['raw_binary_gram'],u,v) for u,v in seed_pairs]
            for (u,v),energy,certificate in zip(seed_pairs,energies,certificates):
                prefix_square=P*(quadratic(row['raw_binary_gram'],u,v)-energy)
                assert 0<=prefix_square<=(B+delta)**2
                assert certificate<=(1+delta)*(B+delta)**2+delta<=bound<1
            assert Q(row['signed_prefix_cost_squared'])<=max(certificates)
            candidates.append({'weight':s,'index':n,'cutoff_multiple':row['cutoff_multiple'],
                               'seed_bound':str(B),'delta':str(delta),'uniform_cost_upper_bound':str(bound),
                               'seed_integer_pairs':[list(x) for x in seed_pairs],
                               'seed_pair_squared_certificates':list(map(str,certificates)),
                               'tail_to_prefix_mass':str(T/P),
                               'scaled_tail_diagonal_maximum':str(mu*max(energies))})
            break
        assert candidates, (s,n,'No tested cutoff met the rational stopping rule')
        best=min(candidates,key=lambda x:Q(x['cutoff_multiple']))
        selected.append(best)
        print(s,n,'certified doubling cutoff',best['cutoff_multiple'],
              'uniform bound',float(bound),flush=True)
    failures=[]
    for row in cases:
        if row['weight']==7 and row['index'] in (8,20,40) and row['cutoff_multiple'] in ('5/4','3','6'):
            v=Q(row['content_only_cost_upper_bound'])
            failures.append({'index':row['index'],'cutoff_multiple':row['cutoff_multiple'],
                             'content_bound_log_per_index':(log(v.numerator)-log(v.denominator))/row['index']})
    (root/'notes/adaptive-prefix-uniform-bound.json').write_text(json.dumps({
        'selected_cases':selected,'content_only_comparison':failures,
        'unscaled_logarithms_negative':True,'strict_negative_normalized_rate_proved':False,
        'rule':'Start K=2n and double until both rational tail inequalities hold.',
        'scope':'Exact finite stopping-rule checks; the all-index termination argument is in the paper.'},indent=2))


if __name__=='__main__':main()
