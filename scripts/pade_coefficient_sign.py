from fractions import Fraction as Q
from functools import lru_cache
from math import comb, factorial
from pathlib import Path
import argparse
import json
import sys
from symmetric_pade_audit import poised_pole_coefficients


@lru_cache(None)
def harmonic(s, n):
    return sum((Q(1, k ** s) for k in range(1, n + 1)), Q(0))


def coefficient_terms(n, m, j):
    magnitude = comb(n, j) ** 5 * comb(j + m, m) * comb(n - j + m, m)
    u = harmonic(1, n - j + m) - harmonic(1, j + m) + \
        6 * (harmonic(1, j) - harmonic(1, n - j))
    v = 6 * (harmonic(2, j) + harmonic(2, n - j)) - \
        harmonic(2, j + m) - harmonic(2, n - j + m)
    amplitude = (u * u + v) / 2
    if n > 0 and m <= n:
        assert v >= 3 * (harmonic(2, j) + harmonic(2, n - j))
        assert amplitude >= Q(3, 2) * harmonic(2, n) > 0
    return (-1) ** (m + j) * magnitude * amplitude


def alpha(n, m):
    return sum((coefficient_terms(n, m, j) for j in range(n + 1)), Q(0))


def main():
    sys.set_int_max_str_digits(200000)
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    pole_checks, kernel_cases = 0, 0
    for n in (2, 4, 6, 8, 12, 20):
        for m in range(n + 1):
            poles = poised_pole_coefficients(2, n, m)
            scale = Q(factorial(n) ** 5, factorial(m) ** 2)
            for j, row in enumerate(poles):
                assert scale * row[3] == coefficient_terms(n, m, j)
                pole_checks += 1
            assert alpha(n, m) == scale * sum(row[3] for row in poles)
            kernel_cases += 1
    rows = []
    for n in range(2, 81, 2):
        a, b = alpha(n, n), alpha(n, n - 1)
        assert a * b < 0
        rows.append({'index': n, 'alpha_n_n': str(a), 'alpha_n_n_minus_one': str(b),
                     'product_negative': True})
    result = {
        'scope': 'Exact harmonic-binomial formula checks and finite global sign checks. '
                 'The local amplitude lower bound is proved in Lean. '
                 'The all-index alternating-sum sign theorem remains unproved.',
        'independent_kernel_cases': kernel_cases,
        'independent_laurent_coefficient_checks': pole_checks,
        'global_adjacent_sign_checks': rows}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2), encoding='utf-8')
    print('kernel cases', kernel_cases, 'Laurent checks', pole_checks,
          'finite adjacent sign checks', len(rows))


if __name__ == '__main__':
    main()
