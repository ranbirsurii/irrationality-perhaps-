"""A separate double-pole derivative construction isolating one odd zeta."""

from fractions import Fraction as Q
from math import comb, factorial, gcd, lcm, prod
from pathlib import Path
import json

from check_integral_cancellation import harmonic
from zeta_enclosure import euler_maclaurin_zeta_interval


def construct(r,n,m):
    assert r>=2 and 1<=m and r*m<=n
    s=2*r+1; d=lcm(*range(1,n+1))
    leading=[]; simple=[]
    for j in range(n+1):
        c=comb(n,j)**2*comb(j+m,m)**(2*r)
        b=c*((2*r+2)*harmonic(j,1)-2*r*harmonic(j+m,1)-2*harmonic(n-j,1))
        assert (d*b).denominator==1
        leading.append(c);simple.append(b)
    assert sum(simple)==0
    for t in (Q(1,2),Q(m+1),Q(n+m+3)):
        direct=Q(factorial(n)**2,factorial(m)**(2*r))*Q(
            prod((t-v)**(2*r) for v in range(1,m+1)),
            prod((t+h)**2 for h in range(n+1)))
        partial=sum((simple[j]/(t+j)+Q(leading[j],1)/(t+j)**2
                     for j in range(n+1)),Q(0))
        assert direct==partial
    A=(s-1)*sum(leading)
    B=-sum(((s-1)*leading[j]*harmonic(j,s)+simple[j]*harmonic(j,s-1)
            for j in range(n+1)),Q(0))
    clearing=d**s
    assert (clearing*B).denominator==1
    g=gcd(clearing*A,int(clearing*B))
    a,b=clearing*A//g,int(clearing*B)//g
    lo,hi=euler_maclaurin_zeta_interval(s,96)
    lo,hi=a*lo+b,a*hi+b
    assert lo<=hi and (lo>0 or hi<0)
    boundary=Q(factorial(2*r),m**(2*r+2)*comb(n+m,m)**2)
    direct_boundary=factorial(2*r)*Q(factorial(n)**2,factorial(m)**(2*r))*Q(
        prod((m-v)**(2*r) for v in range(1,m)),prod((m+h)**2 for h in range(n+1)))
    assert boundary==direct_boundary
    variation_bound=boundary+sum((
        factorial(2*r)*abs(simple[j])/Q(m+j)**(2*r+1)+
        factorial(2*r+1)*leading[j]/Q(m+j)**(2*r+2)
        for j in range(n+1)),Q(0))
    primitive_poisson_bound=Q(clearing,g)*variation_bound/(12*factorial(2*r-1))
    assert max(abs(lo),abs(hi))<=primitive_poisson_bound
    return {'weight':s,'index':n,'zero_length':m,
            'primitive_coefficients':list(map(str,(a,b))),
            'primitive_form_interval':list(map(str,(lo,hi))),
            'interval_excludes_zero':True,'absolute_value_certified_below_one':max(abs(lo),abs(hi))<1,
            'absolute_value_certified_above_one':min(abs(lo),abs(hi))>1,
            'poisson_primitive_majorant':str(primitive_poisson_bound),
            'independent_partial_fraction_checks':True,
            'scope':'Exact finite evaluation of a different pure-target family; no uniform decay or sign theorem.'}


def main():
    data=[]
    for r in (2,3,4):
        for n in (12,24,40):
            for m in sorted({max(1,n//(2*r)),n//r}):
                row=construct(r,n,m);data.append(row)
                print('derivative family',2*r+1,n,m,'below one',row['absolute_value_certified_below_one'],flush=True)
    destination=Path(__file__).resolve().parents[1]/'notes/isolated-derivative-family.json'
    destination.write_text(json.dumps({'cases':data,'uniform_decay_proved':False},indent=2),encoding='utf-8')


if __name__=='__main__':
    main()
