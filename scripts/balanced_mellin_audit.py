from fractions import Fraction as Q
from functools import lru_cache
from math import factorial, gcd, lcm, log, prod
from pathlib import Path
import argparse
import json
import sys
from joint_estimate_audit import H, zeta_interval
from integer_determinants import bareiss, interpolate_integer_values
from integer_determinants import interval_polynomial, polynomial_value
from zeta_enclosure import euler_maclaurin_zeta_interval


@lru_cache(None)
def distinct_moment(exponents):
    assert len(exponents) >= 2 and len(set(exponents)) == len(exponents)
    residues = [Q(1, prod(exponents[j] - e for j in range(len(exponents)) if j != i))
                for i, e in enumerate(exponents)]
    assert sum(residues) == 0
    for k in (1, 2, 7):
        assert sum(c / (k + e) for c, e in zip(residues, exponents)) == \
            Q(1, prod(k + e for e in exponents))
    value = -sum(c * H(e, 1) for c, e in zip(residues, exponents))
    assert value > 0
    return value


def pencil_from_exponents(s, exponents):
    assert all(min(row) >= 0 for row in exponents)
    matrix, slopes = [], []
    for a in exponents:
        row, slope = [], []
        for b in exponents:
            e = tuple(x + y for x, y in zip(a, b))
            if len(set(e)) == 1:
                row.append(-H(e[0], s))
                slope.append(1)
            else:
                assert len(set(e)) == s
                row.append(distinct_moment(e))
                slope.append(0)
        matrix.append(row)
        slopes.append(slope)
    return matrix, slopes


def pencil(s, n, length, base_shift=None):
    r = (s - 1) // 2
    base_shift = r * n if base_shift is None else base_shift
    assert base_shift >= r * n
    indices = [(t, u) for u in range(-n, n + 1) for t in range(length + 1)]
    exponents = [tuple(base_shift + t + (i - r) * u for i in range(s))
                 for t, u in indices]
    return indices, *pencil_from_exponents(s, exponents)


def toric_pencil(s, radius):
    indices = [(j, k) for j in range(radius + 1) for k in range(radius + 1)]
    exponents = [tuple(i * j + (s - 1 - i) * k for i in range(s)) for j, k in indices]
    return indices, *pencil_from_exponents(s, exponents)


def rational_rank(matrix):
    rows = [[Q(x) for x in row] for row in matrix]
    rank = 0
    for j in range(len(rows[0])):
        pivot = next((i for i in range(rank, len(rows)) if rows[i][j]), None)
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        for i in range(rank + 1, len(rows)):
            if rows[i][j]:
                factor = rows[i][j] / rows[rank][j]
                rows[i] = [a - factor * b for a, b in zip(rows[i], rows[rank])]
        rank += 1
        if rank == len(rows):
            break
    return rank


def audit_case(s, n, length, interval, base_shift=None, kind='balanced'):
    if kind == 'toric':
        indices, matrix, slopes = toric_pencil(s, n)
    else:
        indices, matrix, slopes = pencil(s, n, length, base_shift)
    scales = [lcm(*(v.denominator for v in row)) for row in matrix]
    constant = [[int(v * d) for v in row] for row, d in zip(matrix, scales)]
    linear = [[int(v * d) for v in row] for row, d in zip(slopes, scales)]
    degree = 2 * n + 1
    assert rational_rank(linear) == degree
    values = [bareiss([[constant[i][j] + k * linear[i][j] for j in range(len(indices))]
                       for i in range(len(indices))]) for k in range(degree + 1)]
    coefficients = interpolate_integer_values(values)
    assert coefficients[-1] != 0
    k = degree + 1
    extra = bareiss([[constant[i][j] + k * linear[i][j] for j in range(len(indices))]
                     for i in range(len(indices))])
    assert polynomial_value(coefficients, k) == extra
    content = gcd(*coefficients)
    primitive = [c // content for c in coefficients]
    lo, hi = interval_polynomial(primitive, interval)
    order = 96
    while lo <= 0:
        order *= 2
        assert order <= 1536
        lo, hi = interval_polynomial(primitive, euler_maclaurin_zeta_interval(s, order))
    assert 0 < lo <= hi
    row = {'weight': s, 'family': kind, 'anisotropic_radius': n, 'diagonal_degree': length,
           'base_shift': None if kind == 'toric' else
                         (base_shift if base_shift is not None else (s - 1) // 2 * n),
           'matrix_size': len(indices), 'period_polynomial_degree': degree,
           'row_cost': str(prod(scales)), 'polynomial_content': str(content),
           'primitive_polynomial': [str(c) for c in primitive],
           'primitive_value_interval': [str(lo), str(hi)],
           'primitive_value_gt_one': lo > 1,
           'primitive_log_value_per_degree':
               (log((lo + hi).numerator) - log((lo + hi).denominator) - log(2)) / degree}
    print(kind, s, n, length, base_shift, len(indices), degree,
          round(row['primitive_log_value_per_degree'], 6), 'greater than one', lo > 1,
          flush=True)
    return row


def main():
    sys.set_int_max_str_digits(200000)
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--weights', default='3,5,7')
    args = parser.parse_args()
    rows = []
    for s in map(int, args.weights.split(',')):
        interval = euler_maclaurin_zeta_interval(s, 96)
        coarse = zeta_interval(s, 80)
        assert coarse[0] <= interval[0] <= interval[1] <= coarse[1]
        for n, length in ((1, 0), (1, 1), (1, 2), (1, 4), (2, 0), (2, 1), (2, 2),
                          (3, 0), (3, 1), (3, 2)):
            rows.append(audit_case(s, n, length, interval))
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(json.dumps({
                'scope': 'Exact balanced Mellin pencil computations. Finite checks do not '
                         'prove asymptotic smallness or irrationality.',
                'rows': rows}, indent=2), encoding='utf-8')
        r = (s - 1) // 2
        for n in (1, 2):
            for multiplier in (2, 3, 4):
                rows.append(audit_case(s, n, 1, interval, base_shift=multiplier * r * n))
        for n in (1, 2, 3):
            rows.append(audit_case(s, n, n, interval, kind='toric'))
        args.output.write_text(json.dumps({
            'scope': 'Exact primitive-polynomial checks over 57 balanced and toric spaces. '
                     'Finite checks do not establish asymptotic impossibility.',
            'rows': rows}, indent=2), encoding='utf-8')


if __name__ == '__main__':
    main()
