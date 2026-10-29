"""Exact root-partition and adjugate-pencil formulas for the actual forms."""
from fractions import Fraction as Q
from math import factorial,prod,lcm,gcd
from pathlib import Path
import json
from itertools import permutations
from random import Random
from check_integral_cancellation import harmonic,normalized_log_jet_coordinates
from integer_determinants import adjugate_column,bareiss


def partition_coefficient(powers,u,index=1):
    if index>u:return Q(int(u==0))
    return sum((powers[index]**k/factorial(k)*partition_coefficient(powers,u-index*k,index+1)
                for k in range(u//index+1)),Q(0))


def root_laurent_coefficients(s,n,m):
    poles=[Q(-h) for h in range(n+1)]
    roots=[Q(v) for v in range(1,m+1)]+[Q(-n-v) for v in range(1,m+1)]
    rows=[]
    for h,xi in enumerate(poles):
        leading=Q(factorial(n)**s,factorial(m)**2)*prod(xi-rho for rho in roots)/prod(xi-z for z in poles if z!=xi)**s
        powers=[Q(0)]+[Q((-1)**(ell-1),ell)*(sum((1/(xi-rho)**ell for rho in roots),Q(0))
            -s*sum((1/(xi-z)**ell for z in poles if z!=xi),Q(0))) for ell in range(1,s)]
        rows.append([Q(0)]+[leading*partition_coefficient(powers,s-k) for k in range(1,s+1)])
    return rows


def root_coordinates(s,n,m):
    rows=root_laurent_coefficients(s,n,m)
    a=[sum((row[k] for row in rows),Q(0)) for k in range(s+1)]
    b=-sum((rows[h][k]*harmonic(h,k) for h in range(n+1) for k in range(1,s+1)),Q(0))
    return [a[k] for k in range(3,s+1,2)]+[b]


def direct_det(A):
    n=len(A)
    return sum((-1)**sum(p[i]>p[j] for i in range(n) for j in range(i+1,n))
               *prod(A[i][p[i]] for i in range(n)) for p in permutations(range(n)))


def matrix_edge_checks():
    rng=Random(20261029);cases=[]
    for size in range(2,6):
        identity=[[int(i==j) for j in range(size)] for i in range(size)]
        cases.append(identity)
        cases.append([identity[1],identity[0]]+identity[2:])
        for _ in range(12):
            while True:
                B=[[rng.randrange(-3,4) for _ in range(size)] for _ in range(size)]
                if direct_det(B):break
            cases.append(B)
    counters={'matrices':len(cases),'negative_determinants':0,'zero_target_cofactors':0,
              'jacobi_pairs':0,'primitive_root_costs':0}
    for B in cases:
        size=len(B);det=direct_det(B);t=size-2;c=size-1
        U=[(-1)**(t+j)*direct_det([[B[i][k] for k in range(size) if k!=j]
                                  for i in range(size) if i!=t]) for j in range(size)]
        V=[(-1)**(c+j)*direct_det([[B[i][k] for k in range(size) if k!=j]
                                  for i in range(size) if i!=c]) for j in range(size)]
        assert adjugate_column(B,t)==(det,U) and adjugate_column(B,c)==(det,V)
        counters['negative_determinants']+=int(det<0)
        counters['zero_target_cofactors']+=sum(u==0 for u in U)
        for i in range(size):
            for j in range(i+1,size):
                minor=direct_det([[row[k] for k in range(size) if k not in (i,j)] for row in B[:-2]])
                assert U[i]*V[j]-U[j]*V[i]==(-1)**(i+j+1)*det*minor
                counters['jacobi_pairs']+=1
        for p,q in ((0,1),(1,0),(-2,-3),(0,-2),(2,4)):
            w=[p*u+q*v for u,v in zip(U,V)]
            image=[sum(x*y for x,y in zip(row,w)) for row in B]
            assert image==[0]*(size-2)+[det*p,det*q]
            assert gcd(*image[-2:])==abs(det)*gcd(p,q)
            rootmass=abs(q)*sum((abs(u)*abs(Q(p,q)+Q(v,u)) for u,v in zip(U,V) if u),Q(0)) if q else sum(abs(p*u) for u in U)
            if q:rootmass+=abs(q)*sum(abs(v) for u,v in zip(U,V) if not u)
            assert rootmass==sum(map(abs,w))
        for k,u in enumerate(U):
            if not u:continue
            g=gcd(u,V[k]);p=-V[k]//g;q=u//g
            w=[p*x+q*y for x,y in zip(U,V)]
            mass=sum(abs(direct_det([[row[h] for h in range(size) if h not in (j,k)]
                                    for row in B[:-2]])) for j in range(size) if j!=k)
            assert Q(sum(map(abs,w)),abs(det))==Q(mass,g)
            counters['primitive_root_costs']+=1
    return counters


def partial_fraction_checks():
    count=0
    for s in (3,5,7):
        for n in range(6):
            for m in range(n+1):
                rows=root_laurent_coefficients(s,n,m)
                for t in (Q(1,2),Q(n+m+2),Q(2*n+2*m+7,2)):
                    direct=Q(factorial(n)**s,factorial(m)**2)*prod((t-v)*(t+n+v) for v in range(1,m+1))/prod((t+h)**s for h in range(n+1))
                    rebuilt=sum((rows[h][k]/(t+h)**k for h in range(n+1) for k in range(1,s+1)),Q(0))
                    assert direct==rebuilt
                    count+=1
    return count


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
    edge=matrix_edge_checks();reconstructions=partial_fraction_checks()
    path.write_text(json.dumps({'cases':cases,'independent_matrix_edge_checks':edge,
        'direct_partial_fraction_reconstructions':reconstructions,
        'negative_cost_rate_proved':False},indent=2))
    print(len(cases),'root-partition profiles and',4*len(cases),'adjugate/root-mass identities passed')
    print(sum(x['jacobi_root_pair_checks'] for x in cases),'Jacobi root identities;',
          sum(x['exact_root_cost_checks'] for x in cases),'exact primitive root costs')
    print(edge,';',reconstructions,'direct rational-function reconstructions')


if __name__=='__main__':main()
