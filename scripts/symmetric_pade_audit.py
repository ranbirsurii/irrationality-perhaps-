from fractions import Fraction as Q
from functools import lru_cache
from math import comb, gcd, lcm, prod, log
from pathlib import Path
import argparse
import json
import sys
from joint_estimate_audit import H
from zeta_enclosure import euler_maclaurin_zeta_interval


def convolution(a, b, length):
    c = [Q(0)] * length
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            if i + j < length:
                c[i + j] += x * y
    return c


@lru_cache(None)
def pole_coefficients(r, n, m):
    order = 2 * r
    assert r >= 1 and 0 <= m <= r * n
    rows = []
    for j in range(n + 1):
        series = [Q(1)] + [Q(0)] * (order - 1)
        for v in range(1, m + 1):
            series = convolution(series,
                [Q((-j - v) * (n + v - j)), Q(n - 2 * j), Q(1)], order)
        for h in range(n + 1):
            if h != j:
                d = h - j
                series = convolution(series,
                    [Q((-1) ** k * comb(order + k - 1, k), d ** (order + k))
                     for k in range(order)], order)
        rows.append([Q(0)] + [series[order - k] for k in range(1, order + 1)])
    for j in range(n + 1):
        for k in range(1, order + 1):
            assert rows[n - j][k] == (-1) ** k * rows[j][k]
    for t in (Q(1, 2), Q(n + m + 2), Q(n + m + 7, 2)):
        raw = Q(prod((t - v) * (t + n + v) for v in range(1, m + 1)),
                prod((t + j) ** order for j in range(n + 1)))
        expanded = sum((rows[j][k] / (t + j) ** k
                        for j in range(n + 1) for k in range(1, order + 1)), Q(0))
        assert raw == expanded
    return tuple(tuple(row) for row in rows)


def period_coordinates(r, n, m):
    poles = pole_coefficients(r, n, m)
    order = 2 * r
    alpha = {q: sum(((q - 1) * row[q - 1] for row in poles), Q(0))
             for q in range(2, order + 2)}
    assert all(alpha[q] == 0 for q in alpha if q % 2 == 0)
    b = -sum(((q - 1) * poles[j][q - 1] * H(j, q)
              for j in range(n + 1) for q in range(2, order + 2)), Q(0))
    return [alpha[q] for q in range(3, order + 2, 2)] + [b]


@lru_cache(None)
def poised_pole_coefficients(r, n, m):
    order, epsilon = 2 * r + 1, n % 2
    assert 2 * m + epsilon <= order * (n + 1) - 2
    rows = []
    for j in range(n + 1):
        series = [Q(1)] + [Q(0)] * (order - 1)
        if epsilon:
            series = convolution(series, [Q(n - 2 * j), Q(2)], order)
        for v in range(1, m + 1):
            series = convolution(series,
                [Q((-j - v) * (n + v - j)), Q(n - 2 * j), Q(1)], order)
        for h in range(n + 1):
            if h != j:
                d = h - j
                series = convolution(series,
                    [Q((-1) ** k * comb(order + k - 1, k), d ** (order + k))
                     for k in range(order)], order)
        rows.append([Q(0)] + [series[order - k] for k in range(1, order + 1)])
    for j in range(n + 1):
        for k in range(1, order + 1):
            assert rows[n - j][k] == (-1) ** (k + 1) * rows[j][k]
    assert sum(row[1] for row in rows) == 0
    for k in range(1, m + 1):
        assert sum((rows[j][q] / (k + j) ** q
                    for j in range(n + 1) for q in range(1, order + 1)), Q(0)) == 0
    for t in (Q(1, 2), Q(n + m + 2)):
        raw = (2 * t + n) ** epsilon * \
              prod((t - v) * (t + n + v) for v in range(1, m + 1)) / \
              prod((t + j) ** order for j in range(n + 1))
        expanded = sum((rows[j][k] / (t + j) ** k
                        for j in range(n + 1) for k in range(1, order + 1)), Q(0))
        assert raw == expanded
    return tuple(tuple(row) for row in rows)


def poised_period_coordinates(r, n, m):
    poles = poised_pole_coefficients(r, n, m)
    order = 2 * r + 1
    alpha = {q: sum((row[q] for row in poles), Q(0)) for q in range(2, order + 1)}
    assert all(alpha[q] == 0 for q in alpha if q % 2 == 0)
    b = -sum((poles[j][q] * H(j, q)
              for j in range(n + 1) for q in range(1, order + 1)), Q(0))
    return [alpha[q] for q in range(3, order + 1, 2)] + [b]


def one_dimensional_nullvector(matrix, width):
    rows = [row[:] for row in matrix]
    pivots, rank = [], 0
    for j in range(width):
        pivot = next((i for i in range(rank, len(rows)) if rows[i][j]), None)
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        v = rows[rank][j]
        rows[rank] = [x / v for x in rows[rank]]
        for i in range(len(rows)):
            if i != rank:
                v = rows[i][j]
                rows[i] = [x - v * y for x, y in zip(rows[i], rows[rank])]
        pivots.append(j)
        rank += 1
        if rank == len(rows):
            break
    assert rank == width - 1
    free = next(j for j in range(width) if j not in pivots)
    vector = [Q(int(j == free)) for j in range(width)]
    for i, j in enumerate(pivots):
        vector[j] = -rows[i][free]
    d = lcm(*(x.denominator for x in vector))
    integer = [int(d * x) for x in vector]
    content = gcd(*integer)
    integer = [x // content for x in integer]
    assert all(sum(x * y for x, y in zip(row, integer)) == 0 for row in matrix)
    return integer


def audit_case(r, n, gap=1, family='derivative'):
    maximum = r * n if family == 'derivative' else ((2 * r + 1) * (n + 1) - 2 - n % 2) // 2
    shifts = [maximum - gap * j for j in range(r)]
    assert min(shifts) >= 0
    coordinate = period_coordinates if family == 'derivative' else poised_period_coordinates
    data = [coordinate(r, n, m) for m in shifts]
    lower = [[column[k] for column in data] for k in range(r - 1)]
    weights = one_dimensional_nullvector(lower, r)
    combined = [sum((w * column[k] for w, column in zip(weights, data)), Q(0))
                for k in range(r + 1)]
    assert all(c == 0 for c in combined[:r - 1])
    a, b = combined[-2:]
    assert a != 0
    d = lcm(a.denominator, b.denominator)
    u, v = int(d * a), int(d * b)
    content = gcd(abs(u), abs(v))
    u, v = u // content, v // content
    if u < 0:
        u, v = -u, -v
        weights = [-w for w in weights]
        a, b = -a, -b
    order = 96
    while True:
        zlo, zhi = euler_maclaurin_zeta_interval(2 * r + 1, order)
        lo, hi = u * zlo + v, u * zhi + v
        if lo * hi > 0:
            break
        order *= 2
        assert order <= 1536
    lower_abs, upper_abs = min(abs(lo), abs(hi)), max(abs(lo), abs(hi))
    result = {'weight': 2 * r + 1, 'index': n, 'profile_gap': gap, 'family': family,
              'functional_pade_zero_order_at_least': n + min(shifts) + 1
                  if family == 'poised' else None,
              'numerator_block_lengths': shifts,
              'integer_combination': [str(w) for w in weights],
              'combination_one_sign': all(w >= 0 for w in weights) or
                                      all(w <= 0 for w in weights),
              'target_coefficient_before_reduction': str(a),
              'rational_constant_before_reduction': str(b),
              'primitive_target_coefficient': str(u), 'primitive_constant': str(v),
              'primitive_abs_interval': [str(lower_abs), str(upper_abs)],
              'primitive_abs_lt_one': upper_abs < 1,
              'log_primitive_abs_per_index':
                  (log((lower_abs + upper_abs).numerator) -
                   log((lower_abs + upper_abs).denominator) - log(2)) / n}
    print(family, 2 * r + 1, n, gap, 'weight bit lengths', [abs(w).bit_length() for w in weights],
          'primitive < 1', upper_abs < 1,
          'log/n', round(result['log_primitive_abs_per_index'], 6), flush=True)
    return result


def main():
    sys.set_int_max_str_digits(200000)
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    rows = []
    for family in ('derivative', 'poised'):
        for r in (1, 2, 3, 4):
            for n in (1, 2, 3, 5, 8, 12, 20):
                gaps = sorted(set((1, n))) if r > 1 else [1]
                for gap in gaps:
                    rows.append(audit_case(r, n, gap, family))
                    args.output.parent.mkdir(parents=True, exist_ok=True)
                    args.output.write_text(json.dumps({
                        'scope': 'Exact symmetric rational-kernel elimination. Finite smallness '
                                 'or failure is not an irrationality proof or impossibility theorem.',
                        'rows': rows}, indent=2), encoding='utf-8')


if __name__ == '__main__':
    main()
