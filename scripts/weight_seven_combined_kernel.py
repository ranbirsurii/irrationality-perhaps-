"""Exact primitive pairs and joint-kernel intervals; no asymptotic extrapolation."""

from fractions import Fraction as Q
from math import factorial, gcd, lcm, prod
from pathlib import Path
import json
import sys

from check_dual_cost_reduction import dot, reduce_binary_form
from check_integral_cancellation import normalized_log_jet_coordinates
from integer_determinants import adjugate_column
from zeta_enclosure import euler_maclaurin_zeta_interval


def multiply(a, b):
    out = [Q(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i+j] += x*y
    return out


def evaluate(a, x):
    value = Q(0)
    for c in reversed(a):
        value = value*x+c
    return value


def base_term(n, m, k):
    return Q(factorial(n)**7, factorial(m)**2) * Q(
        prod((k-v)*(k+n+v) for v in range(1, m+1)),
        prod((k+h)**7 for h in range(n+1)))


def profile(n, v):
    m = n-3
    result = [Q(0)]*4
    for j in range(4):
        polynomial = [Q(1)]
        for h in range(m+1, n-j+1):
            polynomial = multiply(polynomial, [-h*(n+h), 1])
        scale = v[j]*Q(factorial(m)**2, factorial(n-j)**2)
        for ell, value in enumerate(polynomial):
            result[ell] += scale*value
    assert any(result)
    return result


def combined_interval(n, clearing, v, coefficients, cutoff):
    m = n-3
    exponent = 7*(n+1)-2*m-8
    budget = 2*m*m+7*n*(n+1)
    assert exponent > 0 and cutoff >= max(m+1, 2*m)
    assert cutoff*exponent >= budget
    term = base_term(n, m, m+1)
    partial = Q(0)
    for k in range(m+1, cutoff):
        partial += term*evaluate(coefficients, k*(k+n))
        term *= Q(k**8*(k+n+m+1), (k-m)*(k+n+1)**8)
    assert term == base_term(n, m, cutoff)
    tail = clearing*term*sum((
        abs(c)*(cutoff*(cutoff+n))**ell*(1+Q(cutoff, 7-2*ell))
        for ell, c in enumerate(coefficients)), Q(0))
    center = clearing*partial
    for k in (n-2, n+1, cutoff):
        direct = sum((v[j]*base_term(n, n-j, k) for j in range(4)
                      if k > n-j), Q(0))
        assert base_term(n, m, k)*evaluate(coefficients, k*(k+n)) == direct
    return center-tail, center+tail


def construct(n):
    assert n >= 6 and n % 2 == 0
    D = lcm(*range(1,n+1))**7
    blocks = [normalized_log_jet_coordinates(7,n,n-j) for j in range(4)]
    matrix = [[D*x for x in row] for row in zip(*blocks)]
    assert all(x.denominator == 1 for row in matrix for x in row)
    matrix = [list(map(int,row)) for row in matrix]
    delta, a = adjugate_column(matrix,2)
    again, b = adjugate_column(matrix,3)
    assert delta == again
    reduced,U,steps = reduce_binary_form(dot(a,a),dot(a,b),dot(b,b))
    pair = []
    for col in range(2):
        p,q = U[0][col],U[1][col]
        assert gcd(p,q) == 1
        v = [Q(p*x+q*y,delta) for x,y in zip(a,b)]
        assert [sum(x*y for x,y in zip(row,v)) for row in matrix] == [0,0,p,q]
        clearing = lcm(*(x.denominator for x in v))
        w = [int(clearing*x) for x in v]
        image = [sum(x*y for x,y in zip(row,w)) for row in matrix]
        assert image == [0,0,clearing*p,clearing*q]
        assert gcd(image[2],image[3]) == clearing
        polynomial = profile(n,v)
        lo,hi = combined_interval(n,D,v,polynomial,8*n)
        zlo,zhi=euler_maclaurin_zeta_interval(7,96)
        independent_lo=min(p*zlo,p*zhi)+q
        independent_hi=max(p*zlo,p*zhi)+q
        assert lo <= independent_lo <= independent_hi <= hi
        pair.append({'integer_coefficient_pair':list(map(str,(p,q))),
                     'integer_kernel_vector':list(map(str,w)),
                     'exact_pair_gcd':str(clearing),
                     'normalized_coordinates':list(map(str,v)),
                     'cubic_profile_coefficients':list(map(str,polynomial)),
                     'combined_sum_interval':list(map(str,(lo,hi))),
                     'interval_excludes_zero':lo > 0 or hi < 0,
                     'independent_zeta_interval_contained':True,
                     'interval_inside_unit_interval':max(abs(lo),abs(hi)) < 1})
    assert abs(U[0][0]*U[1][1]-U[0][1]*U[1][0]) == 1
    return {'weight':7,'index':n,'gauss_steps':steps,'pair':pair,
            'unimodular_coefficient_pairs':True,
            'optimal_pair_cost_squared':str(Q(reduced[2],delta*delta)),
            'scope':'Exact finite intervals; the definitions give an all-index algorithm, not a decay theorem.'}


def main():
    sys.set_int_max_str_digits(200000)
    records=[]
    for n in (6,8,12,20,40):
        row=construct(n)
        records.append(row)
        print(n,'Gauss steps',row['gauss_steps'],
              'nonzero intervals',[x['interval_excludes_zero'] for x in row['pair']],
              'bounds below one',[x['interval_inside_unit_interval'] for x in row['pair']],flush=True)
    destination=Path(__file__).resolve().parents[1]/'notes/weight-seven-combined-kernel.json'
    destination.write_text(json.dumps({'cases':records,'uniform_decay_proved':False},indent=2),encoding='utf-8')


if __name__=='__main__':
    main()
