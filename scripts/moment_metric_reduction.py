"""Certified positive-moment upper metric retaining polynomial cross terms."""
from fractions import Fraction as Q
from math import lcm
from pathlib import Path
import json
import sys

from check_integral_cancellation import normalized_log_jet_coordinates
from integer_determinants import adjugate_column
from exact_transition_norm import weighted_profile, mass
from parametric_odd_profiles import kernel
from check_dual_cost_reduction import reduce_binary_form
from zeta_enclosure import euler_maclaurin_zeta_interval


def pairing(x, G, y):
    return sum((x[i]*G[i][j]*y[j] for i in range(len(x)) for j in range(len(y))), Q(0))


def construct(r, n):
    s = 2*r+1
    m = n-r
    K = 3*n
    D = lcm(*range(1, n+1))**s
    blocks = [normalized_log_jet_coordinates(s, n, n-j) for j in range(r+1)]
    matrix_q = [[D*x for x in row] for row in zip(*blocks)]
    assert all(x.denominator == 1 for row in matrix_q for x in row)
    M = [list(map(int, row)) for row in matrix_q]
    delta, a = adjugate_column(M, r-1)
    again, b = adjugate_column(M, r)
    assert delta == again and delta != 0
    u = weighted_profile(r, n, [Q(x, delta) for x in a])
    v = weighted_profile(r, n, [Q(x, delta) for x in b])
    moments = [Q(0)]*(2*r+1)
    peak = Q(0)
    for k in range(m+1, K+1):
        term = kernel(s, n, m, Q(k))
        peak = max(peak, term)
        w = Q(k*(k+n), 12*n*n)
        for ell in range(2*r+1):
            moments[ell] += term*w**ell
    E = s*(n+1)-2*m-(4*r+2)
    B = 2*m*m+s*n*(n+1)
    assert E > 0 and E*K >= B
    last = kernel(s, n, m, Q(K))
    tails = [last*Q(1, 12*n*n)**ell*Q(K+n, K)**ell
             *Q(K**(2*ell+1), 4*r+1-2*ell) for ell in range(2*r+1)]
    G = [[moments[i+j] + ((r+1)*tails[2*i] if i == j else 0)
          for j in range(r+1)] for i in range(r+1)]
    mu = moments[0]+tails[0]
    gram = pairing(u,G,u), pairing(u,G,v), pairing(v,G,v)
    reduced, U, steps = reduce_binary_form(*gram)
    enclosure_order = max(96, 2*n)
    lo, hi = euler_maclaurin_zeta_interval(s, enclosure_order)
    forms = []
    for col in range(2):
        p, q = U[0][col], U[1][col]
        z = [p*x+q*y for x,y in zip(u,v)]
        square_bound = D*D*mu*pairing(z,G,z)
        actual = max(abs(p*lo+q), abs(p*hi+q))
        assert actual*actual <= square_bound
        old = D*mass(z)*(3*n*peak+(3*n+1)*last)
        forms.append({'primitive_pair': [str(p),str(q)],
                      'moment_bound_squared': str(square_bound),
                      'old_same_pair_bound_squared': str(old*old),
                      'old_over_moment_squared': str(old*old/square_bound),
                      'moment_bound_below_one': square_bound < 1})
    return {'weight':s,'index':n,'cutoff':K,'enclosure_order':enclosure_order,
            'gauss_steps':steps,'forms':forms}


def main():
    sys.set_int_max_str_digits(200000)
    records=[]
    for r,n in ((3,6),(3,8),(3,12),(3,20),(3,40),(3,80),(3,160),
                (4,8),(4,12),(4,20),(4,40)):
        row=construct(r,n)
        records.append(row)
        print('moment metric',2*r+1,n,'small bounds',sum(f['moment_bound_below_one'] for f in row['forms']),flush=True)
    root=Path(__file__).resolve().parents[1]
    (root/'notes/moment-metric-reduction.json').write_text(json.dumps({
        'cases':records,'uniform_rate_proved':False,
        'scope':'Exact rational finite metrics with proved infinite-tail envelopes; no rate extrapolation.'},indent=2))


if __name__ == '__main__':
    main()
