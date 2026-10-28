"""Exact integer frame and content checks for the stored primitive cubics."""

from fractions import Fraction as Q
from math import gcd, lcm
from pathlib import Path
import json

from check_integral_cancellation import normalized_log_jet_coordinates
from integer_determinants import bareiss


def main():
    root=Path(__file__).resolve().parents[1]
    source=json.loads((root/'notes/weight-seven-combined-kernel.json').read_text(encoding='utf-8'))
    records=[]
    for row in source['cases']:
        n=row['index']; D=lcm(*range(1,n+1))**7
        blocks=[normalized_log_jet_coordinates(7,n,n-j) for j in range(4)]
        M=[[int(D*x) for x in r] for r in zip(*blocks)]
        delta=bareiss(M)
        a,b,c=(n-2)*(2*n-2),(n-1)*(2*n-1),2*n*n
        s1=n*n; s2=s1*(n-1)**2; F=s2*(n-2)**2
        R=[[-a*b*c,a*b*s1,-a*s2,F],
           [a*b+a*c+b*c,-(a+b)*s1,s2,0],
           [-(a+b+c),s1,0,0],[1,0,0,0]]
        assert bareiss(R)==n**6*(n-1)**4*(n-2)**2
        forms=[]
        for form in row['pair']:
            v=list(map(Q,form['normalized_coordinates']))
            cubic=list(map(Q,form['cubic_profile_coefficients']))
            numerator=[delta*x for x in v]
            assert all(x.denominator==1 for x in numerator)
            numerator=list(map(int,numerator))
            B=[sum(x*y for x,y in zip(r,numerator)) for r in R]
            assert [Q(x,F*delta) for x in B]==cubic
            gC=gcd(*numerator); gB=gcd(*B)
            assert gC>0 and gB%gC==0 and F%(gB//gC)==0
            J=sum((abs(x)*(12*n*n)**ell for ell,x in enumerate(cubic)),Q(0))
            mass=sum(map(abs,v))
            assert mass<=J<=43904*mass
            primitive_height=sum(abs(x//gB)*(12*n*n)**ell for ell,x in enumerate(B))
            assert J==Q(gB*primitive_height,F*abs(delta))
            forms.append({'integer_cramer_numerators':list(map(str,numerator)),
                          'integer_cubic_numerators':list(map(str,B)),
                          'cramer_content':str(gC),'cubic_content':str(gB),
                          'content_quotient_divides_polynomial_F':True,
                          'weighted_primitive_polynomial_height':str(primitive_height),
                          'weighted_cubic_height':str(J),
                          'mass_equivalence_verified':True})
        records.append({'index':n,'F':str(F),'augmented_determinant':str(delta),
                        'frame_determinant':str(bareiss(R)),'forms':forms})
        print(n,'integer frame, exact height ratio, and content bounds verified')
    (root/'notes/cubic-arithmetic-frame.json').write_text(json.dumps({
        'cases':records,'scope':'Finite independent checks of all-index paper identities; '
        'no winning coefficient-growth estimate.'},indent=2),encoding='utf-8')


if __name__=='__main__':
    main()
