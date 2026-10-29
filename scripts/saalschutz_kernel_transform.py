"""Integer Pfaff--Saalschutz decomposition of the unchanged rational kernel."""
from fractions import Fraction as Q
from math import comb, factorial, prod, gcd, isqrt
from pathlib import Path
import json

from weight_seven_combined_kernel import multiply, evaluate
from parametric_odd_profiles import kernel


def rising(x,k):return prod(x+j for j in range(k))


def rising_poly(a,k):
    out=[Q(1)]
    for j in range(k):out=multiply(out,[a+j,1])
    return out


def coefficients(n,m):
    return [(-1)**j*comb(n+2*m+1,m-j)*comb(n+j,j) for j in range(m+1)]


def optimized_mass_bound_squared(n,m):
    if m==0:return Q(1),Q(0)
    scale=10**12
    root=Q(isqrt((n+1)*(n+2*m+1)*scale*scale),scale)
    z=Q(m)/(n+m+1+root)
    assert 0<z<1
    envelope=(1+z)**(n+2*m+1)/(1-z)**(n+1)/z**m
    fourier_factor=Q(11,28)*(1+z)**2/((n+2*m+1)*z)
    return min(envelope**2,envelope**2*fourier_factor),z


def beta_integral(n,m,P):
    # Integrate after u=1-P*x. Every exponent is <=-2, so no log occurs.
    a=n+2*m+2
    first=[Q((-1)**j*comb(m,j)) for j in range(m+1)]
    second=[Q(comb(n,j))*(P-1)**(n-j) for j in range(n+1)]
    polynomial=multiply(first,second)
    return sum((c*(1-(1-P)**(j-a+1))/Q(j-a+1)
                for j,c in enumerate(polynomial)),Q(0))/P**(m+n+1)


def main():
    polynomial_checks=0; integral_checks=0; term_checks=0
    for n in range(15):
        for m in range(n+1):
            c=coefficients(n,m)
            lhs=multiply(rising_poly(-m,m),rising_poly(n+1,m))
            lhs=[comb(2*m,m)*x for x in lhs]
            rhs=[Q(0)]*(2*m+1)
            for j,cj in enumerate(c):
                for i,x in enumerate(rising_poly(-m-j,2*m)):rhs[i]+=cj*x
            assert lhs==rhs
            assert sum(map(abs,c))<=2**m*comb(n+2*m+1,m)
            assert sum(map(abs,c))**2*6**(2*(n-m))<=3*108**n
            assert 14*(n+2*m+1)*sum(map(abs,c))**2*6**(2*(n-m))<=99*108**n
            if 2*m==n:
                assert 7*(2*n+1)*sum(map(abs,c))**2<=44*16**n
            improved,_=optimized_mass_bound_squared(n,m)
            assert sum(map(abs,c))**2<=improved
            assert comb(2*m,m)%gcd(*c)==0
            polynomial_checks+=1
            for P in (Q(1,4),Q(1,2),Q(3,4)):
                transformed=sum((Q(cj)*P**j for j,cj in enumerate(c)),Q(0))
                transformed*=Q(factorial(m)*factorial(n),factorial(n+m+1))
                transformed/=comb(n+2*m+1,m)*(1-P)**(2*m+1)
                assert beta_integral(n,m,P)==transformed
                integral_checks+=1
    records=[]
    for s,n,m in ((5,6,6),(5,12,10),(7,6,3),(7,12,9),(9,8,4),(11,10,5)):
        b=m+1; a=n+2*m+2; B=n+m+2
        assert b+B==a+1 and B-Q(a,2)==Q(n,2)+1
        first=kernel(s,n,m,Q(m+1))
        for j in range(8):
            term=first*Q(rising(b,j)**(s+1)*rising(a,j),rising(B,j)**(s+1)*factorial(j))
            assert term==kernel(s,n,m,Q(m+1+j))
            term_checks+=1
        c=coefficients(n,m)
        for t in (Q(1,2),Q(m+1),Q(2*n+1)):
            transformed=sum((Q(cj)*rising(t-m-j,2*m) for j,cj in enumerate(c)),Q(0))
            transformed*=Q(factorial(n)**s,factorial(2*m))/prod((t+h)**s for h in range(n+1))
            assert transformed==kernel(s,n,m,t)
        records.append({'weight':s,'index':n,'numerator_length':m,
                        'integer_transform_coefficients':list(map(str,c)),
                        'coefficient_l1_mass':str(sum(map(abs,c))),
                        'optimized_mass_bound_squared':str(optimized_mass_bound_squared(n,m)[0])})
    root=Path(__file__).resolve().parents[1]
    (root/'notes/saalschutz-kernel-transform.json').write_text(json.dumps({
        'polynomial_identity_checks':polynomial_checks,'independent_integral_checks':integral_checks,
        'hypergeometric_term_checks':term_checks,'examples':records,
        'required_primitive_cost_rate_proved':False},indent=2))
    print(polynomial_checks,'full polynomial identities;',integral_checks,'independent beta integrals;',term_checks,'hypergeometric terms passed')


if __name__=='__main__':main()
