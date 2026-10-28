"""Exact Smith witnesses and the selected-minor correction, at finite indices."""

import argparse
from fractions import Fraction as Q
from itertools import permutations
import json
from math import gcd
from pathlib import Path

from analytic_sum_control import log_interval
from audit_primitive_normalization import outward_interval


def matmul(a, b):
    return [[sum(x * y for x, y in zip(row, col)) for col in zip(*b)] for row in a]


def determinant(a):
    size = len(a)
    value = 0
    for perm in permutations(range(size)):
        sign = (-1) ** sum(perm[i] > perm[j] for i in range(size) for j in range(i+1, size))
        term = sign
        for i, j in enumerate(perm):
            term *= a[i][j]
        value += term
    return value


def identity(size):
    return [[int(i == j) for j in range(size)] for i in range(size)]


def smith_witness(original):
    a, u, v = [row[:] for row in original], identity(2), identity(3)

    def swap_rows(i, j):
        a[i], a[j] = a[j], a[i]
        u[i], u[j] = u[j], u[i]

    def add_row(i, j, q):
        a[i] = [x + q*y for x, y in zip(a[i], a[j])]
        u[i] = [x + q*y for x, y in zip(u[i], u[j])]

    def swap_columns(i, j):
        for matrix in (a, v):
            for row in matrix:
                row[i], row[j] = row[j], row[i]

    def add_column(i, j, q):
        for matrix in (a, v):
            for row in matrix:
                row[i] += q*row[j]

    for k in range(2):
        positions = [(i, j) for i in range(k, 2) for j in range(k, 3) if a[i][j]]
        assert positions, 'rank must be two'
        i, j = min(positions, key=lambda ij: abs(a[ij[0]][ij[1]]))
        swap_rows(k, i)
        swap_columns(k, j)
        while True:
            below = next((i for i in range(k+1, 2) if a[i][k]), None)
            if below is not None:
                add_row(below, k, -(a[below][k] // a[k][k]))
                if a[below][k]:
                    swap_rows(below, k)
                continue
            right = next((j for j in range(k+1, 3) if a[k][j]), None)
            if right is not None:
                add_column(right, k, -(a[k][right] // a[k][k]))
                if a[k][right]:
                    swap_columns(right, k)
                continue
            offender = next(((i, j) for i in range(k+1, 2) for j in range(k+1, 3)
                             if divmod(a[i][j], a[k][k])[1]), None)
            if offender is None:
                break
            add_row(k, offender[0], 1)
        if a[k][k] < 0:
            a[k] = [-x for x in a[k]]
            u[k] = [-x for x in u[k]]
    assert matmul(matmul(u, original), v) == a
    assert abs(determinant(u)) == abs(determinant(v)) == 1
    assert a == [[a[0][0], 0, 0], [0, a[1][1], 0]]
    assert a[0][0] > 0 and a[1][1] > 0
    assert divmod(a[1][1], a[0][0])[1] == 0
    return a, u, v


def bezout(a, b):
    old_r, r, old_s, s, old_t, t = abs(a), abs(b), 1, 0, 0, 1
    while r:
        q = old_r // r
        old_r, r = r, old_r - q*r
        old_s, s = s, old_s - q*s
        old_t, t = t, old_t - q*t
    x, y = old_s * (-1 if a < 0 else 1), old_t * (-1 if b < 0 else 1)
    assert x*a + y*b == old_r
    return old_r, x, y


def primes_to(n):
    primes = []
    for value in range(2, n+1):
        if all(divmod(value, p)[1] for p in primes if p*p <= value):
            primes.append(value)
    return primes


def valuation(value, p):
    assert value != 0
    value, result = abs(value), 0
    while divmod(value, p)[1] == 0:
        value //= p
        result += 1
    return result


def strings(matrix):
    return [[str(x) for x in row] for row in matrix]


def audit(row):
    n = row['index']
    original = [[int(x) for x in r] for r in row['cleared_coefficient_rows']]
    (x0, y0, z0), (x1, y1, z1) = original
    h, mass, H = int(row['full_gcd']), int(row['weight_mass']), int(row['minor_gcd'])
    third = y0*z1-y1*z0
    delta = gcd(H, third)
    entry_gcd = gcd(*(x for r in original for x in r))
    diagonal, left, right = smith_witness(original)
    assert diagonal[0][0] == entry_gcd
    assert diagonal[0][0] * diagonal[1][1] == delta

    # Row reduction keeping track of the distinguished lower-period column.
    g, a, b = bezout(x0, x1)
    adapted_left = [[a, b], [-x1//g, x0//g]]
    adapted = matmul(adapted_left, original)
    assert adapted[0][0] == g and adapted[1][0] == 0
    c, d = adapted[1][1:]
    hh, aa, bb = bezout(c, d)
    assert hh == h
    adapted_right = [[1, 0, 0], [0, aa, -d//h], [0, bb, c//h]]
    normal = matmul(adapted, adapted_right)
    assert normal[1] == [0, h, 0]
    assert determinant(adapted_left) == determinant(adapted_right) == 1
    t = gcd(g, normal[0][2])
    assert delta == h*t and H == g*h
    excess = H//delta
    assert excess*t == g
    assert Q(h, mass) == Q(delta*excess, abs(x0)+abs(x1))

    entry_divisor = gcd(x1*y0, x0*y1, x1*z0, x0*z1)
    assert divmod(H, entry_divisor)[1] == 0
    residue, local = H, []
    for p in primes_to(n):
        vp = valuation(H, p)
        if vp:
            local.append({'prime': p, 'selected_gcd': vp, 'smith_product': valuation(delta, p),
                          'excess': valuation(excess, p),
                          'entrywise_lower_bound': valuation(entry_divisor, p)})
            residue //= p**vp
    lower_mass = abs(x0)+abs(x1)
    lo, hi = log_interval(Q(delta, lower_mass))
    print(n, 'selected/full', excess, 'log(Smith product / lower row)/n',
          float((lo+hi)/(2*n)), flush=True)
    return {'index': n, 'smith_factors': [str(entry_gcd), str(delta//entry_gcd)],
            'smith_product': str(delta), 'third_minor': str(third),
            'selected_minor_excess': str(excess), 'lower_column_gcd': str(g),
            'smith_left': strings(left), 'smith_right': strings(right),
            'smith_witness_verified': True,
            'adapted_left': strings(adapted_left), 'adapted_right': strings(adapted_right),
            'adapted_normal_form': strings(normal), 'adapted_factor_t': str(t),
            'exact_ratio_identity_verified': True,
            'entrywise_common_divisor': str(entry_divisor),
            'prime_ledger_through_index': local,
            'selected_gcd_residual_after_small_primes': str(residue),
            'log_smith_product_to_lower_row_per_index_interval': outward_interval(lo/n, hi/n)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    data = json.loads((root/'notes/primitive-normalization-audit.json').read_text())
    rows = [audit(row) for row in data['cases']]
    args.output.write_text(json.dumps({
        'scope': 'Finite exact unimodular Smith witnesses and adapted lattice identities. '
                 'No limiting arithmetic estimate or irrationality conclusion.',
        'cases': rows}, indent=2))


if __name__ == '__main__':
    main()
