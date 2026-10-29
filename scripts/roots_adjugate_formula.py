"""Exact root-partition and adjugate-pencil formulas for the actual forms."""
from fractions import Fraction as Q
from math import factorial,prod,lcm,gcd
from pathlib import Path
import json
from check_integral_cancellation import harmonic,normalized_log_jet_coordinates
from integer_determinants import adjugate_column,bareiss


def partition_coefficient(powers,u,index=1):
    if index>u:return Q(int(u==0))
    return sum((powers[index]**k/factorial(k)*partition_coefficient(powers,u-index*k,index+1)
                for k in range(u//index+1)),Q(0))


def root_coordinates(s,n,m):
    poles=[Q(-h) for h in range(n+1)]
    roots=[Q(v) for v in range(1,m+1)]+[Q(-n-v) for v in range(1,m+1)]
    a=[Q(0)]*(s+1);b=Q(0)
    for h,xi in enumerate(poles):
        leading=Q(factorial(n)**s,factorial(m)**2)*prod(xi-rho for rho in roots)/prod(xi-z for z in poles if z!=xi)**s
        powers=[Q(0)]+[Q((-1)**(ell-1),ell)*(sum((1/(xi-rho)**ell for rho in roots),Q(0))
            -s*sum((1/(xi-z)**ell for z in poles if z!=xi),Q(0))) for ell in range(1,s)]
        for k in range(1,s+1):
            value=leading*partition_coefficient(powers,s-k)
            a[k]+=value;b-=value*harmonic(h,k)
    return [a[k] for k in range(3,s+1,2)]+[b]


def check(s,n):
    r=(s-1)//2;D=lcm(*range(1,n+1))**s
    cols=[root_coordinates(s,n,n-j) for j in range(r+1)]
    assert all(c==normalized_log_jet_coordinates(s,n,n-j) for j,c in enumerate(cols))
    B=[[D*c[i] for c in cols] for i in range(r+1)]
    assert all(x.denominator==1 for row in B for x in row)
    B=[[int(x) for x in row] for row in B]
    determinant,U=adjugate_column(B,r-1);determinant2,V=adjugate_column(B,r)
    assert determinant==determinant2
    rootlist=[(j,-Q(v,u)) for j,(u,v) in enumerate(zip(U,V)) if u]
    pair_checks=0;root_cost_checks=0
    for i in range(r+1):
        for j in range(i+1,r+1):
            minor=bareiss([[row[k] for k in range(r+1) if k not in (i,j)] for row in B[:-2]])
            assert U[i]*V[j]-U[j]*V[i]==(-1)**(i+j+1)*determinant*minor
            pair_checks+=1
    for k in range(r+1):
        if not U[k]:continue
        g=gcd(U[k],V[k]);p=-V[k]//g;q=U[k]//g
        w=[p*u+q*v for u,v in zip(U,V)]
        minor_mass=sum(abs(bareiss([[row[h] for h in range(r+1) if h not in (j,k)]
                                   for row in B[:-2]])) for j in range(r+1) if j!=k)
        assert w[k]==0 and gcd(p,q)==1
        assert Q(sum(map(abs,w)),abs(determinant))==Q(minor_mass,g)
        root_cost_checks+=1
    for p,q in ((-1,1),(2,3),(7,5),(2,4)):
        w=[p*u+q*v for u,v in zip(U,V)]
        image=[sum(x*y for x,y in zip(row,w)) for row in B]
        assert image==[0]*(r-1)+[determinant*p,determinant*q]
        assert gcd(*image[-2:])==abs(determinant)*gcd(p,q)
        rootmass=q*sum((abs(U[j])*abs(Q(p,q)-rho) for j,rho in rootlist),Q(0))
        rootmass+=q*sum(abs(v) for u,v in zip(U,V) if not u)
        assert rootmass==sum(map(abs,w))
    return {'weight':s,'index':n,'root_partition_formula_verified':True,
        'adjugate_pencil_and_primitive_content_verified':True,
        'weighted_root_mass_verified':True,'determinant':str(determinant),
        'jacobi_root_pair_checks':pair_checks,'exact_root_cost_checks':root_cost_checks,
        'pencil_roots':[{'coordinate':j,'root':str(rho)} for j,rho in rootlist]}


def main():
    cases=[check(s,n) for s,n in ((7,6),(7,8),(7,12),(9,8),(9,12),(11,10))]
    path=Path(__file__).resolve().parents[1]/'notes/roots-adjugate-formula.json'
    path.write_text(json.dumps({'cases':cases,'negative_cost_rate_proved':False},indent=2))
    print(len(cases),'root-partition profiles and',4*len(cases),'adjugate/root-mass identities passed')
    print(sum(x['jacobi_root_pair_checks'] for x in cases),'Jacobi root identities;',
          sum(x['exact_root_cost_checks'] for x in cases),'exact primitive root costs')


if __name__=='__main__':main()
