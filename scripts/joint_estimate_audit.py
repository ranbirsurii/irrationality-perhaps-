from fractions import Fraction as Q
from math import comb, gcd, log, lcm
from functools import lru_cache
from pathlib import Path
import json, argparse

@lru_cache(None)
def H(n,s):
    return sum((Q(1,j**s) for j in range(1,n+1)),Q(0))

def data(n):
    A=B=C=E=Q(0)
    terms=[]
    for k in range(n+1):
        a=Q(comb(n,k)**2*comb(n+k,k)**2)
        eta=H(n+k,1)+H(n-k,1)-2*H(k,1)
        second=H(n+k,2)-2*H(k,2)-H(n-k,2)
        third=-H(n+k,3)+2*H(k,3)-H(n-k,3)
        reg0=2*eta**2-second
        reg1=-Q(4,3)*eta**3+2*eta*second+Q(2,3)*third
        pole0=H(k,2)+H(n-k,2)
        pole1=2*H(k,3)-2*H(n-k,3)
        p4=-a; p3=2*a*eta; p2=-a*(reg0+pole0)
        p1=-a*(reg1-2*eta*pole0+pole1)
        e=-(4*p4*H(k,5)+3*p3*H(k,4)+2*p2*H(k,3)+p1*H(k,2))
        A+=a
        B+=a*(2*H(k,3)-2*eta*H(k,2))
        C+=-2*a*(2*eta**2-H(n+k,2)+3*H(k,2)+2*H(n-k,2))
        E+=e
        terms.append(e)
    return A,B,C,E,terms

@lru_cache(None)
def halfH(k,s):
    return sum((Q(2**s,(2*j+1)**s) for j in range(k)),Q(0))

def half_rational_part(n):
    total=Q(0)
    for k in range(n+1):
        a=Q(comb(n,k)**2*comb(n+k,k)**2)
        e=H(n+k,1)+H(n-k,1)-2*H(k,1)
        d2=H(n+k,2)-2*H(k,2)-H(n-k,2)
        d3=-H(n+k,3)+2*H(k,3)-H(n-k,3)
        v0=2*e*e-d2
        v1=-Q(4,3)*e**3+2*e*d2+Q(2,3)*d3
        w0=H(k,2)+H(n-k,2)
        w1=2*H(k,3)-2*H(n-k,3)
        p4=-a; p3=2*a*e; p2=-a*(v0+w0); p1=-a*(v1-2*e*w0+w1)
        total-=4*p4*halfH(k,5)+3*p3*halfH(k,4)+2*p2*halfH(k,3)+p1*halfH(k,2)
    return total

def negative_derivative_first_coefficient(n,t):
    numerator=denominator=Q(1)
    for j in range(1,n+1): numerator*=t-j
    for j in range(n+1): denominator*=t+j
    F=(numerator/denominator)**2
    ld=2*(sum((1/(t-j) for j in range(1,n+1)),Q(0))-
          sum((1/(t+j) for j in range(n+1)),Q(0)))
    s2=sum((1/(t+j)**2 for j in range(n+1)),Q(0))
    s3=sum((1/(t+j)**3 for j in range(n+1)),Q(0))
    return F*(ld*s2-2*s3)

def zeta_interval(s,N):
    row=[Q(1,(j+1)**s) for j in range(N)]
    eta=Q(0)
    for k in range(N):
        assert 0 < row[0] <= 1
        eta+=row[0]/2**(k+1)
        row=[row[j]-row[j+1] for j in range(len(row)-1)]
    scale=1-Q(1,2**(s-1))
    return eta/scale,(eta+Q(1,2**N))/scale

def logq(x):
    return log(abs(x.numerator))-log(x.denominator)

def audit(a,b,zlo,zhi,n):
    lo,hi=(a*zlo+b,a*zhi+b) if a>=0 else (a*zhi+b,a*zlo+b)
    assert lo*hi>0
    den=lcm(a.denominator,b.denominator)
    assert (a*den).denominator == 1
    ai=int(a*den); bi=int(b*den)
    g=gcd(abs(ai),abs(bi))
    plo,phi=lo*den/g,hi*den/g
    lower=min(abs(plo),abs(phi)); upper=max(abs(plo),abs(phi))
    return {'a':str(a),'b':str(b),'primitive_a':str(ai//g),'primitive_b':str(bi//g),
            'raw_decay_exponent':-logq((abs(lo)+abs(hi))/2)/n,
            'primitive_decay_exponent':-logq((lower+upper)/2)/n,
            'normalization_exponent':(log(den)-log(g))/n,
            'primitive_abs_gt_one':lower>1,
            'primitive_abs_lower':str(lower),'primitive_abs_upper':str(upper)}

def determinant(matrix):
    a=[row[:] for row in matrix]
    result=Q(1)
    for i in range(len(a)):
        pivot=next((j for j in range(i,len(a)) if a[j][i]),None)
        if pivot is None: return Q(0)
        if pivot!=i:
            a[i],a[pivot]=a[pivot],a[i]
            result=-result
        p=a[i][i]
        result*=p
        for j in range(i+1,len(a)):
            c=a[j][i]/p
            for k in range(i+1,len(a)):
                a[j][k]-=c*a[i][k]
            a[j][i]=Q(0)
    return result

def hankel_coefficients(n,shift=0):
    b=determinant([[-H(shift+i+j,5) for j in range(n)] for i in range(n)])
    at_one=determinant([[1-H(shift+i+j,5) for j in range(n)] for i in range(n)])
    a=at_one-b
    minor=determinant([[Q(1,(shift+i+j+1)**5)-Q(1,(shift+i+j+2)**5)
                        for j in range(n-1)] for i in range(n-1)])
    assert a==minor
    return a,b

if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    N=600
    zlo,zhi=zeta_interval(5,N)
    rows=[]
    for n in [1,2,3,5,10,20,30,40]:
        A,B,C,E,_=data(n)
        early=sum((negative_derivative_first_coefficient(n,Q(2*j+1,2))
                   for j in range(n)),Q(0))
        tailE=half_rational_part(n)-early
        forms={'displayed_adams':(-4*A,-Q(7,24)*E),
               'scalar_elimination':(-8*A*A,2*A*E+C*B),
               'half_grid_full':(-96*A,half_rational_part(n)-7*E),
               'half_grid_tail':(-96*A,tailE-7*E)}
        row={'n':n,'forms':{k:audit(a,b,zlo,zhi,n) for k,(a,b) in forms.items()}}
        rows.append(row)
        print('n',n,[(k,round(v['raw_decay_exponent'],6),
                        round(v['primitive_decay_exponent'],6),v['primitive_abs_gt_one'])
                       for k,v in row['forms'].items()])
    hankel=[]
    for n in [2,3,5,8,10,15,20]:
        a,b=hankel_coefficients(n)
        v=audit(a,b,zlo,zhi,n*n)
        hankel.append({'n':n,'form':v})
        print('Hankel',n,'per n^2:',round(v['raw_decay_exponent'],6),
              round(v['primitive_decay_exponent'],6),v['primitive_abs_gt_one'])
    shifted_hankel=[]
    for n in [10,20]:
        for multiplier in [1,2,3,4]:
            shift=multiplier*n
            a,b=hankel_coefficients(n,shift)
            v=audit(a,b,zlo,zhi,n*n)
            shifted_hankel.append({'n':n,'shift':shift,'form':v})
            print('Shifted Hankel',n,shift,'per n^2:',round(v['raw_decay_exponent'],6),
                  round(v['primitive_decay_exponent'],6),v['primitive_abs_gt_one'])
    result={'zeta_interval_method':'Euler transform of eta(5), positive coefficient tail <= 2^-N',
            'terms':N,'zeta_lower':str(zlo),'zeta_upper':str(zhi),'rows':rows,'hankel_rows':hankel,
            'shifted_hankel_rows':shifted_hankel,
            'scope':'Finite exact rational interval audit; no asymptotic inference.'}
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(result,indent=2))
