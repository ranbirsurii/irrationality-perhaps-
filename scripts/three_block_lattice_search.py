"""Finite positive three-block lattice search with exact primitive-form bounds."""

import argparse
from fractions import Fraction as Q
import json
from math import factorial, gcd, lcm, prod
from pathlib import Path
import sys

from analytic_sum_control import log_interval
from audit_primitive_normalization import outward_interval, weight_five_coordinates
from audit_smith_lattice import bezout, determinant


def dot(a, b):
    return sum(x*y for x, y in zip(a, b))


def cross(a, b):
    return [a[1]*b[2]-a[2]*b[1], a[2]*b[0]-a[0]*b[2], a[0]*b[1]-a[1]*b[0]]


def gauss_reduce(a, b):
    while True:
        if dot(b, b) < dot(a, a):
            a, b = b, a
        q = (2*dot(a, b)+dot(a, a)) // (2*dot(a, a))
        if q == 0:
            assert dot(a, a) <= dot(b, b)
            assert 2*abs(dot(a, b)) <= dot(a, a)
            return a, b
        b = [y-q*x for x, y in zip(a, b)]


def saturated_kernel_basis(x):
    g, u, v = bezout(x[0], x[1])
    h = gcd(g, x[2])
    assert g > 0 and h > 0
    a = [x[1]//g, -x[0]//g, 0]
    b = [u*(x[2]//h), v*(x[2]//h), -g//h]
    assert dot(x, a) == dot(x, b) == 0
    a, b = gauss_reduce(a, b)
    primitive_normal = [value//h for value in x]
    assert cross(a, b) in (primitive_normal, [-value for value in primitive_normal])
    return a, b


def positive_rounding_weights(x, a, b):
    positive = sum(max(value, 0) for value in x)
    negative = sum(max(-value, 0) for value in x)
    assert positive > 0 and negative > 0
    interior = [negative if value >= 0 else positive for value in x]
    assert dot(x, interior) == 0
    aa, ab, bb = dot(a, a), dot(a, b), dot(b, b)
    gram_determinant = aa*bb-ab*ab
    assert gram_determinant > 0
    av, bv = dot(a, interior), dot(b, interior)
    coordinates = [Q(bb*av-ab*bv, gram_determinant),
                   Q(aa*bv-ab*av, gram_determinant)]
    assert all(value.denominator == 1 for value in coordinates)
    covering_twice = max(abs(u)+abs(v) for u, v in zip(a, b))
    assert covering_twice > 0
    scale = Q(covering_twice, min(interior))
    targets = [scale*value+Q(1, 2) for value in coordinates]
    s, t = [value.numerator//value.denominator for value in targets]
    weights = [s*u+t*v for u, v in zip(a, b)]
    assert all(value > 0 for value in weights)
    assert dot(x, weights) == 0
    common = gcd(*weights)
    return [value//common for value in weights]


def lattice_arithmetic_bound(rows, a, b, w, clearing):
    x = [row[0] for row in rows]
    images = [[sum(vector[i]*rows[i][j] for i in range(3)) for j in (1, 2)]
              for vector in (a, b)]
    gamma = gcd(*(value for pair in images for value in pair))
    minors = [x[i]*rows[j][q]-x[j]*rows[i][q]
              for i in range(3) for j in range(i+1, 3) for q in (1, 2)]
    assert gamma > 0 and gcd(*minors) == gcd(*x)*gamma
    aa, ab, bb = dot(a, a), dot(a, b), dot(b, b)
    wa, wb = dot(w, a), dot(w, b)
    gram = aa*bb-ab*ab
    s, sr = divmod(wa*bb-wb*ab, gram)
    t, tr = divmod(wb*aa-wa*ab, gram)
    assert sr == tr == 0
    assert list(w) == [s*z+t*zz for z, zz in zip(a, b)]
    radius = max(abs(s), abs(t))
    basis_mass = sum(map(abs, a))+sum(map(abs, b))
    bound = Q(clearing*radius*basis_mass, gamma)
    output = [sum(w[i]*rows[i][j] for i in range(3)) for j in (1, 2)]
    content = gcd(*output)
    assert divmod(content, gamma)[1] == 0
    assert Q(clearing*sum(w), content) <= bound
    return {'kernel_image_content': str(gamma),
            'selected_basis_coordinates': [str(s), str(t)],
            'selected_basis_radius': str(radius), 'basis_l1_mass': str(basis_mass),
            'uniform_lattice_cost_upper_bound': str(bound)}


def positive_sum_bounds(n, m):
    exponent = 5*(n+1)-2*m-2
    budget = 2*m*m+5*n*(n+1)
    cutoff = max(2*m, m+1, (budget+exponent-1)//exponent)

    def decreasing(k):
        return k**6*(k+n+m+1) <= (k-m)*(k+n+1)**6

    assert decreasing(cutoff)
    lo, hi = m+1, cutoff
    while lo < hi:
        mid = (lo+hi)//2
        if decreasing(mid):
            hi = mid
        else:
            lo = mid+1
    peak_index = lo
    assert decreasing(peak_index)
    assert peak_index == m+1 or not decreasing(peak_index-1)
    peak = Q(factorial(n)**5 * factorial(peak_index-1)**6
             * factorial(peak_index+n+m),
             factorial(m)**2 * factorial(peak_index-m-1)
             * factorial(peak_index+n)**6)
    assert peak > 0
    if n <= 20:
        direct = Q(factorial(n)**5, factorial(m)**2) * Q(
            prod((peak_index-v)*(peak_index+n+v) for v in range(1, m+1)),
            prod((peak_index+j)**5 for j in range(n+1)))
        assert direct == peak
    return peak, (2*cutoff+1)*peak, {'length': m, 'peak_index': peak_index, 'cutoff': cutoff}


def search(n, radius):
    assert n >= 2 and not (n & 1)
    clearing = lcm(*range(1, n+1))**5
    rational_rows = [weight_five_coordinates(n, n-j) for j in range(3)]
    rows = [[clearing*x for x in row] for row in rational_rows]
    assert all(x.denominator == 1 for row in rows for x in row)
    rows = [list(map(int, row)) for row in rows]
    x = [row[0] for row in rows]
    assert x[0]*x[1] < 0
    a, b = saturated_kernel_basis(x)
    candidates = set()

    def consider(w):
        if all(value <= 0 for value in w):
            w = [-value for value in w]
        if all(value >= 0 for value in w) and any(w):
            g = gcd(*w)
            candidates.add(tuple(value//g for value in w))

    rounding_weights = positive_rounding_weights(x, a, b)
    consider(rounding_weights)
    for i in range(3):
        if x[i] == 0:
            consider([int(j == i) for j in range(3)])
        for j in range(i+1, 3):
            if x[i]*x[j] < 0:
                g = gcd(x[i], x[j])
                w = [0, 0, 0]
                w[i], w[j] = abs(x[j])//g, abs(x[i])//g
                consider(w)
    for s in range(-radius, radius+1):
        for t in range(-radius, radius+1):
            if gcd(s, t) == 1:
                consider([s*z+t*zz for z, zz in zip(a, b)])
    best = None
    for w in sorted(candidates):
        assert dot(w, x) == 0 and gcd(*w) == 1
        aa, bb = [sum(w[i]*rows[i][j] for i in range(3)) for j in (1, 2)]
        content = gcd(aa, bb)
        assert content > 0
        cost = Q(clearing*sum(w), content)
        candidate = (cost, w, content, aa//content, bb//content)
        if best is None or cost < best[0]:
            best = candidate
    cost, w, content, aa, bb = best
    bounds = [positive_sum_bounds(n, n-j) for j in range(3)]
    lower = Q(clearing, content)*sum(w[i]*bounds[i][0] for i in range(3))
    upper = Q(clearing, content)*sum(w[i]*bounds[i][1] for i in range(3))
    rhs_upper = cost*max(pair[1] for pair in bounds)
    assert 0 < lower <= upper <= rhs_upper
    costlog = log_interval(cost)
    upperlog = log_interval(upper)
    rhslog = log_interval(rhs_upper)
    print(n, 'log K / n', float(sum(costlog)/(2*n)),
          'log primitive upper / n', float(sum(upperlog)/(2*n)),
          'certified below one', upper < 1, flush=True)
    lattice = lattice_arithmetic_bound(rows, a, b, w, clearing)
    lattice_log = log_interval(Q(lattice['uniform_lattice_cost_upper_bound']))
    lattice['log_uniform_lattice_cost_upper_per_index_interval'] = outward_interval(
        lattice_log[0]/n, lattice_log[1]/n)
    saving = Q(int(lattice['selected_basis_radius'])*int(lattice['basis_l1_mass']),
               int(lattice['kernel_image_content']))
    saving_log = log_interval(saving)
    lattice['lattice_saving_rate_interval'] = outward_interval(saving_log[0]/n, saving_log[1]/n)
    return {'index': n, 'profile': [n, n-1, n-2], 'search_radius': radius,
            'candidate_count': len(candidates),
            'scope': 'Best cost among the finite box, two-block rays, and constructive '
                     'positive rounding vector; no global optimality.',
            'positive_rounding_weights': list(map(str, rounding_weights)),
            'cleared_coordinate_rows': [[str(value) for value in row] for row in rows],
            'coefficient_matrix_determinant': str(determinant(rows)),
            'saturated_gauss_basis': [[str(value) for value in vector] for vector in (a, b)],
            'positive_primitive_weights': list(map(str, w)),
            'weight_mass': str(sum(w)), 'clearing_factor': str(clearing),
            'removed_content': str(content), 'exact_primitive_cost': str(cost),
            'primitive_target_coefficient': str(aa), 'primitive_constant': str(bb),
            'sum_bound_parameters': [pair[2] for pair in bounds],
            'exact_primitive_form_lower_bound': str(lower),
            'exact_primitive_form_upper_bound': str(upper),
            'exact_rhs_upper_bound': str(rhs_upper),
            'primitive_form_certified_positive_and_below_one': upper < 1,
            'rhs_certified_below_one': rhs_upper < 1,
            'log_cost_per_index_interval': outward_interval(costlog[0]/n, costlog[1]/n),
            'log_primitive_upper_per_index_interval': outward_interval(upperlog[0]/n, upperlog[1]/n),
            'log_rhs_upper_per_index_interval': outward_interval(rhslog[0]/n, rhslog[1]/n),
            **lattice}


def main():
    sys.set_int_max_str_digits(200000)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--radius', type=int, default=20)
    parser.add_argument('--indices', type=int, nargs='+',
                        default=[2,4,8,12,20,40,80,160,320,640,1280])
    args = parser.parse_args()
    data = {'scope': 'Finite exact positive three-block forms and rational sum bounds. '
                     'No all-index arithmetic estimate or irrationality theorem.',
            'cases': [search(n, args.radius) for n in args.indices]}
    args.output.write_text(json.dumps(data, indent=2))


if __name__ == '__main__':
    main()
