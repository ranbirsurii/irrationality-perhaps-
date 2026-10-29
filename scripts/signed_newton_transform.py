"""Exact signed Newton transform, including actual Laurent-coordinate amplitudes."""
from fractions import Fraction as Q
from math import comb,factorial
from pathlib import Path
import json,sys
from check_integral_cancellation import harmonic,normalized_log_jet_coordinates
from saalschutz_kernel_transform import coefficients


def differences(values):
    out=[]
    while values:
        out.append(values[0]);values=[b-a for a,b in zip(values,values[1:])]
    return out


def branch_coordinates(s,n,m,j,length=None):
    length=2*m if length is None else length
    sums=[Q(0)]*(s+1);constant=Q(0)
    for h in range(n+1):
        numerator=[Q(1)]+[Q(0)]*(s-1)
        for v in range(length):
            c=-h-m-j+v
            numerator=[c*numerator[0]]+[c*numerator[k]+numerator[k-1] for k in range(1,s)]
        logarithms=[Q(0)]+[s*(harmonic(h,k)+(-1)**k*harmonic(n-h,k)) for k in range(1,s)]
        unit=[Q(1)]
        for u in range(1,s):
            unit.append(sum((logarithms[k]*unit[u-k] for k in range(1,u+1)),Q(0))/u)
        scale=Q((-1)**(s*h)*comb(n,h)**s,factorial(length))
        for q in range(1,s+1):
            value=scale*sum((numerator[i]*unit[s-q-i] for i in range(s-q+1)),Q(0))
            sums[q]+=value;constant-=value*harmonic(h,q)
    return sums[1:]+[constant]


def rising(x,k):
    value=Q(1)
    for j in range(k):
        value*=x+j
    return value


def pole_cauchy_bounds(s,n,m):
    rho=Q(1,2*(n+1))
    bounds=[Q(0)]*(s+1)
    for h in range(n+1):
        denominator=rising(1-rho,h)*rising(1-rho,n-h)
        numerator=rising(h+1+rho,m)*rising(n-h+1+rho,m)
        circle=Q(factorial(n)**s,factorial(m)**2)*numerator/denominator**s
        for q in range(1,s+1):
            term=circle*rho**(q-s)
            bounds[q-1]+=term
            bounds[-1]+=term*harmonic(h,q)
    return bounds


def main():
    sys.set_int_max_str_digits(200000)
    moment_checks=0
    for n in range(21):
        for m in range(n+1):
            c=coefficients(n,m)
            assert sum(c)==comb(2*m,m)
            for k in range(m+1):
                assert sum(c[j]*comb(j,k) for j in range(k,m+1))==(-1)**k*comb(n+k,k)*comb(2*m-k,m-k)
                moment_checks+=1
    convex_checks=0
    for n in range(21):
        for m in range(n+1):
            for t in (Q(m+1),Q(2*n+1),Q(6*n+1,2)):
                probabilities=[comb(m,k)*rising(n+1,k)*rising(t,m-k)/rising(t+n+1,m)
                               for k in range(m+1)]
                assert min(probabilities)>=0 and sum(probabilities)==1
                convex_checks+=1
    records=[]
    for s,n in ((7,6),(7,8),(9,8),(11,10)):
        for offset in (0,1):
            m=n-offset;c=coefficients(n,m)
            branches=[branch_coordinates(s,n,m,j) for j in range(m+1)]
            direct=[sum((c[j]*branches[j][i] for j in range(m+1)),Q(0)) for i in range(s+1)]
            via=[];bounds=[]
            closed=[branch_coordinates(s,n,m,0,2*m-k) for k in range(m+1)]
            for i in range(s+1):
                ds=differences([x[i] for x in branches])
                assert all(ds[k]==(-1)**k*closed[k][i] for k in range(m+1))
                terms=[(-1)**k*comb(n+k,k)*comb(2*m-k,m-k)*ds[k] for k in range(m+1)]
                via.append(sum(terms,Q(0)));bounds.append(sum(map(abs,terms),Q(0)))
            expected=normalized_log_jet_coordinates(s,n,m)
            assert via==direct
            assert [direct[q-1] for q in range(3,s+1,2)]+[direct[-1]]==expected
            assert direct[0]==0 and all(direct[q-1]==0 for q in range(2,s+1,2))
            cauchy=pole_cauchy_bounds(s,n,m)
            assert all(abs(value)<=bound for value,bound in zip(direct,cauchy))
            records.append({'weight':s,'index':n,'numerator_length':m,
                            'signed_mass':str(sum(c)),'absolute_mass':str(sum(map(abs,c))),
                            'all_laurent_coordinates_verified':True,'all_order_difference_formula_verified':True,
                            'direct_pole_cauchy_bound_verified':True,
                            'newton_triangle_bounds':list(map(str,bounds))})
    root=Path(__file__).resolve().parents[1]
    (root/'notes/signed-newton-transform.json').write_text(json.dumps({
        'moment_checks':moment_checks,'convex_identity_checks':convex_checks,
        'actual_coordinate_cases':records,
        'required_primitive_cost_rate_proved':False},indent=2))
    print(moment_checks,'exact moment checks;',convex_checks,'convex identities;',
          len(records),'full Laurent transformations and pole bounds passed')


if __name__=='__main__':main()
