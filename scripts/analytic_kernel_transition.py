"""Exact raw-kernel index transition and clearing-free moment identity."""
from fractions import Fraction as Q
from math import prod
from pathlib import Path
import json
from parametric_odd_profiles import kernel
from moment_metric_reduction import construct


def shift(s,n,m,t):
    return (Q(((n+1)*(n+2))**s,((m+1)*(m+2))**2)
            * (t*(t+1))**(s+1)
            * prod(t+n+m+j for j in range(1,7))
            / prod((t+n+j)**(s+1) for j in range(1,5)))


def main():
    q0=Q(64*8**16*5**10,13**26)
    assert 2304*q0 < Q(1,100)
    records=[]
    for r in (3,4,5,6,8,10):
        s=2*r+1
        for n in (2*r,4*r):
            m=n-r
            for t in (Q(m+1),Q(n+1),Q(3*n),Q(2*n+1,2)):
                assert kernel(s,n+2,m+2,t+2) == kernel(s,n,m,t)*shift(s,n,m,t)
                if n >= 4*r:
                    assert shift(s,n,m,t) <= Q(1,100)*Q(1,16)**(s-7)
            data=construct(r,n)
            value=Q(data['kernel_mass_majorant'])*Q(data['raw_reduced_second'])
            assert value==Q(data['full_moment_bound'])
            assert value==max(Q(x['moment_bound_squared']) for x in data['forms'])
            records.append({'weight':s,'index':n,'clearing_free_product':str(value),
                            'kernel_shift_checks':4,'exact_reduction_scale_identity':True})
    root=Path(__file__).resolve().parents[1]
    (root/'notes/analytic-kernel-transition.json').write_text(json.dumps({
        'cases':records,'uniform_decay_proved':False},indent=2))
    print(len(records),'clearing-free metric identities and',4*len(records),'kernel shifts passed')


if __name__=='__main__':
    main()
