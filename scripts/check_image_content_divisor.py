"""Exact checks of the image-content divisor proved in the companion note."""
from fractions import Fraction as Q
from functools import lru_cache
from itertools import combinations
from math import comb,gcd,lcm,prod
from pathlib import Path
import json
from audit_smith_lattice import primes_to
from check_integral_cancellation import harmonic,normalized_log_jet_coordinates
from integer_determinants import bareiss
from signed_newton_transform import branch_coordinates
from saalschutz_kernel_transform import coefficients


@lru_cache(None)
def raw_coordinates(s,n,m):
    sums=[Q(0)]*(s+1);constant=Q(0)
    for h in range(n+1):
        leading=(-1)**(m+h)*comb(n,h)**s*comb(h+m,m)*comb(n-h+m,m)
        logjet=[Q(0)]+[(-1)**(k-1)*( (-1)**k*harmonic(h+m,k)
            +harmonic(n-h+m,k)-(s+1)*((-1)**k*harmonic(h,k)+harmonic(n-h,k)))
            for k in range(1,s)]
        jet=[Q(1)]
        for u in range(1,s):
            jet.append(sum((logjet[k]*jet[u-k] for k in range(1,u+1)),Q(0))/u)
        for k in range(1,s+1):
            value=leading*jet[s-k]
            sums[k]+=value;constant-=value*harmonic(h,k)
    return [sums[k] for k in range(3,s+1,2)]+[constant]


def mod(x,p):
    x=Q(x)
    assert x.denominator%p
    return x.numerator*pow(x.denominator,-1,p)%p


def minor_gcd(rows):
    return gcd(*(bareiss([[row[j] for j in I] for row in rows])
        for I in combinations(range(len(rows[0])),len(rows))))


def check(s,n):
    r=(s-1)//2;d=lcm(*range(1,n+1));D=d**s
    columns=[raw_coordinates(s,n,n-j) for j in range(r+1)]
    assert all(c==normalized_log_jet_coordinates(s,n,n-j) for j,c in enumerate(columns))
    primes=primes_to((s-2)*n//2)
    eligible=[p for p in primes if p<=n and p>s and p*p>3*n+2*r+3
        and all((n-j)%p for j in range(r+1))
        and all((3*n-j)%p for j in range(2*r+3))]
    P=prod(eligible);A=1;congruences=0
    for p in eligible:
        q,a=divmod(n,p)
        for j,column in enumerate(columns):
            b=a-j
            top=sum((-1)**(b+h)*comb(a,h)**s*comb(h+b,b)*comb(a-h+b,b)
                    for h in range(a+1))
            small=raw_coordinates(s,q,q)
            scaled=[p**(s-k)*column[(k-3)//2] for k in range(3,s+1,2)]
            scaled.append(p**s*column[-1])
            assert [mod(x,p) for x in scaled]==[mod(top*x,p) for x in small],(s,n,p,j)
            if q%2 or 3*a>=2*p:
                assert mod(top,p)==0
            congruences+=1
        carry=(3*n)//(2*p)-3*(n//(2*p))
        if carry>0:A*=p
    G={k:prod(p for p in primes if n<p<=(s-2)*n//(k-1)) for k in range(3,s-1,2)}
    C=[[d**(s-k)*column[(k-3)//2]/G[k] for column in columns]
       for k in range(3,s-1,2)]
    Y=[D*column[-2] for column in columns];Z=[D*column[-1] for column in columns]
    assert all(x.denominator==1 for row in C+[Y,Z] for x in row)
    C=[[int(x) for x in row] for row in C];Y=list(map(int,Y));Z=list(map(int,Z))
    delta=minor_gcd(C)
    joint=gcd(minor_gcd(C+[Y]),minor_gcd(C+[Z]))
    assert delta>0 and joint>0 and joint%delta==0
    gamma=joint//delta
    assert gamma%A==0
    assert joint%(P**(r-1)*A)==0
    I=next(I for I in combinations(range(r+1),r-1)
           if bareiss([[row[j] for j in I] for row in C]))
    square=[[row[j] for j in I] for row in C]
    determinant=bareiss(square)
    vectors=[]
    for free in set(range(r+1))-set(I):
        w=[0]*(r+1);w[free]=determinant
        for k,pivot in enumerate(I):
            changed=[row[:] for row in square]
            for i in range(r-1):changed[i][k]=C[i][free]
            w[pivot]=-bareiss(changed)
        assert all(x%delta==0 for x in w)
        v=[x//delta for x in w]
        assert all(sum(x*y for x,y in zip(row,v))==0 for row in C)
        assert sum(x*y for x,y in zip(Y,v))%gamma==0
        assert sum(x*y for x,y in zip(Z,v))%gamma==0
        assert Q(sum(map(abs,v)),gamma)==Q(sum(map(abs,w)),joint)
        vectors.append(v)
    return {'weight':s,'index':n,'eligible_primes':eligible,
        'first_order_congruence_checks':congruences,'image_content_divisor':str(A),
        'actual_image_content':str(gamma),'joint_determinantal_divisor':str(P**(r-1)*A),
        'actual_joint_determinantal_content':str(joint),
        'primitive_cramer_ratio_identity_verified':True}


def main():
    small_checks=0
    for s in (5,7,9):
        for n in range(5):
            for m in range(n+1):
                weights=coefficients(n,m)
                branches=[branch_coordinates(s,n,m,j) for j in range(m+1)]
                full=[sum((weights[j]*branches[j][i] for j in range(m+1)),Q(0))
                      for i in range(s+1)]
                assert raw_coordinates(s,n,m)==[full[k-1] for k in range(3,s+1,2)]+[full[-1]]
                small_checks+=1
    records=[check(s,n) for s,n in ((7,40),(7,60),(7,80),(7,100),(7,120),
                                  (9,60),(9,80),(11,60))]
    result={'scope':'Exact finite checks of the separate all-index paper proof.',
        'cases':records,'independent_small_raw_kernel_checks':small_checks,
        'required_negative_relative_cost_rate_proved':False}
    path=Path(__file__).resolve().parents[1]/'notes/image-content-prime-divisor.json'
    path.write_text(json.dumps(result,indent=2))
    print(len(records),'content and primitive Cramer checks;',
          sum(x['first_order_congruence_checks'] for x in records),'local congruences;',
          small_checks,'independent small raw-kernel checks')


if __name__=='__main__':main()
