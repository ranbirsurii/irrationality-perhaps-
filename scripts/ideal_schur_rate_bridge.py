"""Exact ideal-norm identities and finite analytic tests of a 1/100 rate target."""
from fractions import Fraction as Q
from math import gcd,isqrt,lcm
from pathlib import Path
import json,sys


def main():
    sys.set_int_max_str_digits(200000)
    root=Path(__file__).resolve().parents[1]
    data=json.loads((root/'notes/signed-prefix-metric.json').read_text())['cases']
    results=[]
    for row in data:
        A,B,C=map(Q,row['raw_binary_gram']);mu=Q(row['kernel_mass_majorant'])
        alpha=Q(row['raw_reduced_gram'][0]);det=A*C-B*B
        d=lcm(A.denominator,(2*B).denominator,C.denominator)
        integers=[int(d*x) for x in (A,2*B,C)];g=gcd(*integers)
        a,b,c=[x//g for x in integers];eta=Q(g,d);disc=4*a*c-b*b
        m=alpha/eta
        assert a>0 and disc>0 and m.denominator==1 and m>=1
        assert det==eta*eta*disc/4
        assert Q(row['scalar_sandwich_lower'])==mu*eta*disc/(4*m)
        x,y=map(int,row['forms'][0]['pair'])
        assert a*x*x+b*x*y+c*y*y==m
        norm=Q(a*x)+Q(b*y,2)
        assert norm*norm+Q(disc*y*y,4)==a*m
        n=row['index'];T=mu*det*Q(100,99)**n
        h=det/A;theta=B/A
        assert A>=T
        radius2=T/h
        end=isqrt(radius2.numerator//radius2.denominator)+1
        tested=[]
        for v in range(1,end+1):
            if h*v*v>=T:continue
            t=theta*v;floor=t.numerator//t.denominator
            distance=min(t-floor,1-(t-floor))
            value=A*distance*distance+h*v*v
            assert value>=T
            tested.append(v)
        assert alpha>=T
        results.append({'weight':row['weight'],'index':n,'cutoff_multiple':row['cutoff_multiple'],
                        'integer_slices_tested':tested,'primitive_ideal_norm_identity':True,
                        'rate_base':'99/100','finite_epsilon_test_passed':True})
    out={'cases':results,'all_index_epsilon_bound_proved':False,
         'scope':'Exact finite Schur tests and ideal identities; no extrapolation to larger indices.'}
    (root/'notes/ideal-schur-rate-bridge.json').write_text(json.dumps(out,indent=2))
    print(len(results),'exact norm identities and finite epsilon tests passed; maximum slice count',
          max(len(x['integer_slices_tested']) for x in results))


if __name__=='__main__':main()
