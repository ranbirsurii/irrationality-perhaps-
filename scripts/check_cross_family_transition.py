"""Transfer pure-target derivative forms into the original Pade family exactly."""

from fractions import Fraction as Q
from math import factorial, gcd, lcm
from pathlib import Path
import json

from check_integral_cancellation import normalized_log_jet_coordinates
from integer_determinants import adjugate_column
from weight_seven_combined_kernel import multiply


def main():
    root=Path(__file__).resolve().parents[1]
    source=json.loads((root/'notes/isolated-derivative-family.json').read_text(encoding='utf-8'))
    cache={}; records=[]
    for row in source['cases']:
        s,n=row['weight'],row['index']; r=(s-1)//2
        D=lcm(*range(1,n+1))**s
        key=(s,n)
        if key not in cache:
            blocks=[normalized_log_jet_coordinates(s,n,n-j) for j in range(r+1)]
            M=[[int(D*x) for x in rr] for rr in zip(*blocks)]
            delta,a=adjugate_column(M,r-1);again,b=adjugate_column(M,r)
            assert delta==again
            cache[key]=(M,delta,a,b)
        M,delta,a,b=cache[key]
        p,q=map(int,row['primitive_coefficients'])
        v=[Q(p*x+q*y,delta) for x,y in zip(a,b)]
        assert [sum(x*y for x,y in zip(rr,v)) for rr in M]==[0]*(r-1)+[p,q]
        t=lcm(*(x.denominator for x in v)); w=[int(t*x) for x in v]
        image=[sum(x*y for x,y in zip(rr,w)) for rr in M]
        assert image==[0]*(r-1)+[t*p,t*q]
        assert gcd(image[-2],image[-1])==t
        profile=[Q(0)]*(r+1)
        for j in range(r+1):
            polynomial=[Q(1)]
            for h in range(n-r+1,n-j+1):
                polynomial=multiply(polynomial,[-h*(n+h),1])
            scale=v[j]*Q(factorial(n-r)**2,factorial(n-j)**2)
            for ell,x in enumerate(polynomial):profile[ell]+=scale*x
        height=sum((abs(x)*(12*n*n)**ell for ell,x in enumerate(profile)),Q(0))
        base=140 if s==5 else 2397*4**(s-7)
        constant=12*5**(2*s)*3**(2*s+(s+1)*r)
        bound=constant*(n+1)**(2*s+2)*D*height/Q(base)**n
        lo,hi=map(Q,row['primitive_form_interval'])
        assert max(abs(lo),abs(hi))<=bound
        records.append({'weight':s,'index':n,'derivative_zero_length':row['zero_length'],
                        'transferred_integer_vector':list(map(str,w)),
                        'transferred_coefficient_gcd':str(t),
                        'original_family_weighted_profile_height':str(height),
                        'original_family_analytic_majorant':str(bound),
                        'exact_primitive_period_pair_preserved':True,
                        'transferred_majorant_below_one':bound<1})
    destination=root/'notes/cross-family-transition.json'
    destination.write_text(json.dumps({'cases':records,
        'scope':'Exact transitions and full-cost checks; no uniform transfer norm bound.'},indent=2),encoding='utf-8')
    print(len(records),'cross-family primitive identities verified; small majorants:',
          sum(x['transferred_majorant_below_one'] for x in records))


if __name__=='__main__':
    main()
