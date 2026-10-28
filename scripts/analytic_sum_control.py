from fractions import Fraction as Q
from functools import lru_cache
from math import factorial, prod
from pathlib import Path
import argparse
import json
import sys
from symmetric_pade_audit import poised_period_coordinates
from zeta_enclosure import euler_maclaurin_zeta_interval


@lru_cache(None)
def unit_log_interval(x, terms=32):
    assert 1 <= x <= 2
    z = (x - 1) / (x + 1)
    total, power = Q(0), z
    for k in range(terms):
        total += 2 * power / (2 * k + 1)
        power *= z * z
    error = 2 * power / ((2 * terms + 1) * (1 - z * z))
    return total, total + error


def log_interval(x):
    assert x > 0
    exponent = x.numerator.bit_length() - x.denominator.bit_length()
    if x < Q(2) ** exponent:
        exponent -= 1
    y = x / Q(2) ** exponent
    lo, hi = unit_log_interval(y)
    a, b = unit_log_interval(Q(2))
    return lo + min(exponent * a, exponent * b), hi + max(exponent * a, exponent * b)


def multiply_interval(a, b):
    values = [x * y for x in a for y in b]
    return min(values), max(values)


def xlogx_interval(a, b):
    return multiply_interval((a, b), (log_interval(a)[0], log_interval(b)[1]))


def saddle_certificate(s, beta):
    lo, hi = beta / (1 + beta), Q(1)
    def g(v):
        return beta * (1 + v ** (s + 1)) - sum(v ** k for k in range(1, s + 1))
    assert g(lo) > 0 and g(hi) < 0
    for _ in range(80):
        mid = (lo + hi) / 2
        if g(mid) > 0:
            lo = mid
        else:
            hi = mid
    assert g(lo) >= 0 and g(hi) <= 0
    xlo, xhi = lo / (1 - lo), hi / (1 - hi)
    pieces = [(s + 1, xlogx_interval(xlo, xhi)),
              (-(s + 1), xlogx_interval(xlo + 1, xhi + 1)),
              (1, xlogx_interval(xlo + 1 + beta, xhi + 1 + beta)),
              (-1, xlogx_interval(xlo - beta, xhi - beta)),
              (-2 * beta, log_interval(beta))]
    bounds = [Q(0), Q(0)]
    for c, pair in pieces:
        bounds[0] += min(c * pair[0], c * pair[1])
        bounds[1] += max(c * pair[0], c * pair[1])
    assert bounds[1] < 0
    return {'weight': s, 'beta': str(beta), 'saddle_x_interval': [str(xlo), str(xhi)],
            'analytic_rate_interval': [str(x) for x in bounds],
            'rate_is_negative': True, 'rate_midpoint': float(sum(bounds) / 2)}


def finite_sum_certificate(s, n, m):
    assert n % 2 == 0 and s >= 3 and s % 2 == 1
    E, B = s * (n + 1) - 2 * m - 2, 2 * m * m + s * n * (n + 1)
    assert E > 0
    cutoff = max(2 * m, (B + E - 1) // E, m + 1)
    scale = Q(factorial(n) ** s, factorial(m) ** 2)
    k = m + 1
    term = scale * Q(prod((k - v) * (k + n + v) for v in range(1, m + 1)),
                     prod((k + j) ** s for j in range(n + 1)))
    partial, peak, peak_index = Q(0), term, k
    while k < cutoff:
        partial += term
        term *= Q(k ** (s + 1) * (k + n + m + 1),
                  (k - m) * (k + n + 1) ** (s + 1))
        k += 1
        if term > peak:
            peak, peak_index = term, k
    lower, upper = partial + term, partial + (cutoff + 1) * term
    assert 0 < lower <= upper <= (2 * cutoff + 1) * peak
    coordinates = [q * scale for q in poised_period_coordinates((s - 1) // 2, n, m)]
    order = 96
    while True:
        a, b = coordinates[-1], coordinates[-1]
        for i, coefficient in enumerate(coordinates[:-1]):
            zlo, zhi = euler_maclaurin_zeta_interval(2 * i + 3, order)
            a += min(coefficient * zlo, coefficient * zhi)
            b += max(coefficient * zlo, coefficient * zhi)
        if a > 0:
            break
        order *= 2
        assert order <= 1536
    assert lower <= b and a <= upper
    return {'weight': s, 'index': n, 'block_length': m, 'cutoff': cutoff,
            'peak_index': peak_index, 'normalized_sum_interval': [str(lower), str(upper)],
            'period_interval': [str(a), str(b)],
            'log_sum_per_index_interval': [str(log_interval(lower)[0] / n),
                                           str(log_interval(upper)[1] / n)]}


def main():
    sys.set_int_max_str_digits(200000)
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    saddles, finite = [], []
    for s in (3, 5, 7, 9):
        for k in range(1, 2 * s):
            beta = Q(k, 4)
            if 2 * beta >= s:
                continue
            row = saddle_certificate(s, beta)
            saddles.append(row)
            print(s, beta, round(row['rate_midpoint'], 9), flush=True)
        for beta in sorted(set((Q(1, 2), Q(1), Q(s - 1, 2)))):
            for n in (10, 20):
                finite.append(finite_sum_certificate(s, n, int(beta * n)))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps({
        'scope': 'Exact saddle-root/log intervals and finite positive-sum bounds. '
                 'The asymptotic sum theorem is proved in the note; no primitive-height conclusion.',
        'saddles': saddles, 'finite_sums': finite}, indent=2), encoding='utf-8')


if __name__ == '__main__':
    main()
