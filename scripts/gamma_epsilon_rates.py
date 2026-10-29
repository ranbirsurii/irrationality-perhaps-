"""Rigorous finite-index enclosures of the actual arithmetic and distortion rates."""
from fractions import Fraction as Q
from math import gcd, lcm
from pathlib import Path
import json
import sys

from analytic_sum_control import unit_log_interval
from audit_primitive_normalization import outward_interval


def logarithm(x):
    assert x>0
    exponent=x.numerator.bit_length()-x.denominator.bit_length()
    if x<Q(2)**exponent:exponent-=1
    y=x/Q(2)**exponent
    scale=2**96
    lower=(y*scale).numerator//(y*scale).denominator
    lo,hi=Q(lower,scale),Q(lower+1,scale)
    assert 1<=lo<=y<=hi<=2
    a,b=unit_log_interval(Q(2))
    return (unit_log_interval(lo)[0]+min(exponent*a,exponent*b),
            unit_log_interval(hi)[1]+max(exponent*a,exponent*b))


def dot(a,b):return sum(x*y for x,y in zip(a,b))


def main():
    sys.set_int_max_str_digits(200000)
    root=Path(__file__).resolve().parents[1]
    source=json.loads((root/'notes/three-block-lattice-audit.json').read_text())['cases']
    rows=[]
    for row in source:
        n=row['index']
        a,b=([int(x) for x in v] for v in row['saturated_gauss_basis'])
        A,B,C=dot(a,a),dot(a,b),dot(b,b)
        assert 0<A<=C and 2*abs(B)<=A
        data=[list(map(int,rr)) for rr in row['cleared_coordinate_rows']]
        x,y,z=[list(col) for col in zip(*data)]
        normal=[t//gcd(*x) for t in x]
        N=dot(normal,normal)
        assert A*C-B*B==N
        Gamma=gcd(dot(y,a),gcd(dot(y,b),gcd(dot(z,a),dot(z,b))))
        assert Gamma==int(row['kernel_image_content']) and Gamma>0
        lg=logarithm(Q(Gamma))
        lk=logarithm(Q(C,A))
        ln=logarithm(Q(N))
        le=logarithm(Q(C*N,A))
        gamma=tuple(v/n for v in lg)
        kappa_rate=tuple(v/(2*n) for v in lk)
        normal_rate=tuple(v/(2*n) for v in ln)
        epsilon=tuple(v/(2*n) for v in le)
        assert epsilon[0]<=kappa_rate[1]+normal_rate[1]
        assert epsilon[1]>=kappa_rate[0]+normal_rate[0]
        d=lcm(*range(1,n+1))
        ld=logarithm(Q(d))
        denominator=tuple(5*v/n for v in ld)
        # Constants and the older residual factor are not included in this core.
        core=(denominator[0]-gamma[1]+epsilon[0]/2,
              denominator[1]-gamma[0]+epsilon[1]/2)
        rows.append({'weight':5,'index':n,
            'gamma_n_interval':outward_interval(*gamma),
            'epsilon_n_interval':outward_interval(*epsilon),
            'kappa_rate_interval':outward_interval(*kappa_rate),
            'primitive_normal_rate_interval':outward_interval(*normal_rate),
            'denominator_rate_interval':outward_interval(*denominator),
            'finite_core_cost_rate_interval':outward_interval(*core)})
        if n>=80:
            print(n,'gamma',tuple(float(Q(x)) for x in rows[-1]['gamma_n_interval']),
                  'epsilon',tuple(float(Q(x)) for x in rows[-1]['epsilon_n_interval']))
    (root/'notes/gamma-epsilon-rates.json').write_text(json.dumps({
        'cases':rows,'asymptotic_gamma_lower_bound_proved':False,
        'required_asymptotic_epsilon_upper_bound_proved':False,
        'scope':'Rigorous finite rates for the original weight-five three-block lattice.'},indent=2))


if __name__=='__main__':main()
