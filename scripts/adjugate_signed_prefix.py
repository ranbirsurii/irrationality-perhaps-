"""Cancellation-preserving rational certificates for adjugate root forms."""
from fractions import Fraction as Q
from math import factorial,prod,lcm,gcd
from pathlib import Path
import json
from roots_adjugate_formula import root_coordinates
from integer_determinants import adjugate_column
from weight_seven_combined_kernel import multiply,evaluate
from zeta_enclosure import euler_maclaurin_zeta_interval


def kernel(s,n,m,t):
    return Q(factorial(n)**s,factorial(m)**2)*prod((t-v)*(t+n+v) for v in range(1,m+1))/prod((t+h)**s for h in range(n+1))


def filter_polynomial(s,n,w,det,D):
    r=(s-1)//2;m0=n-r;H=[Q(0)]*(r+1)
    for j,weight in enumerate(w):
        m=n-j;basis=[Q(1)]
        for v in range(m0+1,m+1):basis=multiply(basis,[-v*(n+v),1])
        scale=Q(D*weight*factorial(m0)**2,det*factorial(m)**2)
        for ell,value in enumerate(basis):H[ell]+=scale*value
    return H


def tail_bound(s,n,H,K):
    r=(s-1)//2;m0=n-r;alpha=s*(n+1)-2*n
    assert alpha>1 and K>=max(1,m0+1)
    C=Q(factorial(n)**s,factorial(m0)**2)*(1+Q(n+m0,K))**m0
    V=sum((abs(H[ell])*(1+Q(n,K))**ell/Q(K**(2*(r-ell))) for ell in range(r+1)),Q(0))
    return C*V/Q((alpha-1)*K**(alpha-1))


def check(s,n):
    r=(s-1)//2;m0=n-r;D=lcm(*range(1,n+1))**s
    cols=[root_coordinates(s,n,n-j) for j in range(r+1)]
    assert all((D*c[i]).denominator==1 for c in cols for i in range(r+1))
    B=[[int(D*c[i]) for c in cols] for i in range(r+1)]
    det,U=adjugate_column(B,r-1);_,V=adjugate_column(B,r)
    rootpairs=[]
    for u,v in zip(U,V):
        if not u:continue
        g=gcd(u,v);p=-v//g;q=u//g
        if q<0:p,q=-p,-q
        rootpairs.append((p,q))
    chosen=min(rootpairs,key=lambda pair:max(map(abs,pair)))
    records=[]
    for p,q in ((-1,1),chosen):
        assert gcd(p,q)==1
        w=[p*u+q*v for u,v in zip(U,V)]
        H=filter_polynomial(s,n,w,det,D)
        for t in (Q(m0+1),Q(n+2),Q(2*n+1)):
            direct=Q(D,det)*sum((weight*kernel(s,n,n-j,t) for j,weight in enumerate(w)),Q(0))
            assert kernel(s,n,m0,t)*evaluate(H,t*(t+n))==direct
        eta=Q(1,4**n);K=n+1
        while tail_bound(s,n,H,K)>eta:K*=2
        tail=tail_bound(s,n,H,K)
        prefix=sum((kernel(s,n,m0,Q(t))*evaluate(H,Q(t*(t+n))) for t in range(m0+1,K+1)),Q(0))
        R=abs(prefix)+tail
        zl,zh=euler_maclaurin_zeta_interval(s,96)
        lo,hi=sorted((p*zl+q,p*zh+q))
        assert prefix-tail<=lo<=hi<=prefix+tail
        minabs=min(abs(lo),abs(hi)) if lo*hi>0 else Q(0)
        assert max(abs(lo),abs(hi))<=R
        assert R-minabs<=2*eta+(hi-lo)
        records.append({'pair':[str(p),str(q)],'cutoff':K,'tail_bound':str(tail),
            'tolerance':str(eta),'signed_prefix_majorant':str(R),
            'independent_zeta_enclosure_verified':True,'finite_form_nonzero':lo*hi>0})
    return {'weight':s,'index':n,'certificates':records}


def main():
    cases=[check(s,n) for s,n in ((7,6),(7,8),(7,12),(9,8))]
    path=Path(__file__).resolve().parents[1]/'notes/adjugate-signed-prefix.json'
    path.write_text(json.dumps({'cases':cases,'uniform_decay_proved':False},indent=2))
    print(sum(len(c['certificates']) for c in cases),'exact signed-prefix certificates;',
          'all tails <= 4^(-n); all independent enclosures agree')


if __name__=='__main__':main()
