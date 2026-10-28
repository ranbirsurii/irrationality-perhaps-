from fractions import Fraction as Q
from functools import lru_cache
from math import comb, factorial, gcd, lcm, prod
from pathlib import Path
import argparse
import json
import sys

from analytic_sum_control import log_interval
from symmetric_pade_audit import (
    one_dimensional_nullvector, poised_period_coordinates, poised_pole_coefficients)


@lru_cache(None)
def initial_lcm(n):
    return lcm(*range(1, n + 1))


def check_coefficients(s, n, m):
    r, d = (s - 1) // 2, initial_lcm(n)
    scale = Q(factorial(n) ** s, factorial(m) ** 2)
    rows = poised_pole_coefficients(r, n, m)
    checks = 0
    for j, row in enumerate(rows):
        magnitude = comb(n, j) ** s * comb(j + m, m) * comb(n - j + m, m)
        assert scale * row[s] == (-1) ** (m + j) * magnitude
        for q in range(1, s + 1):
            assert (d ** (s - q) * scale * row[q]).denominator == 1
            checks += 1
    coefficients = [scale * x for x in poised_period_coordinates(r, n, m)]
    for q, coefficient in zip(range(3, s + 1, 2), coefficients[:-1]):
        assert (d ** (s - q) * coefficient).denominator == 1
    assert (d ** s * coefficients[-1]).denominator == 1
    return {
        'weight': s, 'index': n, 'block_length': m,
        'coefficient_checks': checks, 'lcm_n': str(d),
        'full_period_denominator': str(lcm(*(x.denominator for x in coefficients))),
        'proved_clearing_factor': str(d ** s)}


def combined_ledger(s, n):
    r, d = (s - 1) // 2, initial_lcm(n)
    profile = [n - j for j in range(r)]
    assert min(profile) >= 0
    coefficients = [
        [Q(factorial(n) ** s, factorial(m) ** 2) * x
         for x in poised_period_coordinates(r, n, m)] for m in profile]
    clearing = d ** s
    integer = [[int(clearing * x) for x in row] for row in coefficients]
    assert all(Q(z) == clearing * x for row, zs in zip(coefficients, integer)
               for x, z in zip(row, zs))
    lower = [[Q(row[q]) for row in integer] for q in range(r - 1)]
    weights = one_dimensional_nullvector(lower, r)
    combined = [sum(w * row[q] for w, row in zip(weights, integer))
                for q in range(r + 1)]
    assert not any(combined[:-2])
    a, b = combined[-2:]
    assert a != 0
    if a < 0:
        weights, a, b = [-w for w in weights], -a, -b
    content, mass = gcd(a, b), sum(abs(w) for w in weights)
    cost = Q(clearing * mass, content)
    rational_a = sum(w * row[-2] for w, row in zip(weights, coefficients)) / mass
    rational_b = sum(w * row[-1] for w, row in zip(weights, coefficients)) / mass
    assert cost * rational_a == a // content
    assert cost * rational_b == b // content
    larger = initial_lcm(n + max(profile)) ** s
    assert larger % clearing == 0
    multiplier = larger // clearing
    larger_gcd = gcd(multiplier * a, multiplier * b)
    assert larger_gcd == multiplier * content
    assert Q(larger * mass, larger_gcd) == cost
    poles = [poised_pole_coefficients(r, n, m) for m in profile]
    scales = [Q(factorial(n) ** s, factorial(m) ** 2) for m in profile]
    combined_poles = [[sum(Q(w, mass) * scale * pole[j][q]
                          for w, scale, pole in zip(weights, scales, poles))
                       for q in range(s + 1)] for j in range(n + 1)]
    totals = [sum(row[q] for row in combined_poles) for q in range(s + 1)]
    assert all(value == (rational_a if q == s else 0) for q, value in enumerate(totals))
    telescoper, running = [], [-value for value in totals]
    for row in combined_poles[:-1]:
        running = [a + b for a, b in zip(running, row)]
        telescoper.append(running[:])
    for j, row in enumerate(combined_poles):
        for q in range(1, s + 1):
            reconstructed = ((totals[q] if j == 0 else 0) +
                             (telescoper[j][q] if j < n else 0) -
                             (telescoper[j - 1][q] if j else 0))
            assert row[q] == reconstructed
    def g_value(t):
        return sum(row[q] / (t + j) ** q for j, row in enumerate(telescoper)
                   for q in range(1, s + 1))
    assert g_value(Q(1)) == rational_b
    for t in (Q(1, 2), Q(n + 2), Q(2 * n + 3)):
        actual = sum(Q(w, mass) * scale *
                     Q(prod((t - v) * (t + n + v) for v in range(1, m + 1)),
                       prod((t + j) ** s for j in range(n + 1)))
                     for w, scale, m in zip(weights, scales, profile))
        assert actual == rational_a / t ** s + g_value(t) - g_value(t + 1)
    lo, hi = log_interval(cost)
    one_sign = all(w >= 0 for w in weights) or all(w <= 0 for w in weights)
    print(s, n, 'one-sign', one_sign, 'log cost / n', round(float((lo + hi) / (2 * n)), 6),
          flush=True)
    return {
        'weight': s, 'index': n, 'profile': profile,
        'primitive_integer_weights': list(map(str, weights)),
        'combination_one_sign': one_sign, 'weight_mass': str(mass),
        'clearing_factor': str(clearing), 'removed_full_gcd': str(content),
        'primitive_target': str(a // content), 'primitive_constant': str(b // content),
        'exact_primitive_cost': str(cost),
        'normalized_target': str(rational_a), 'normalized_constant': str(rational_b),
        'telescoper_coefficients': [[str(x) for x in row] for row in telescoper],
        'telescoper_at_one_equals_constant': True,
        'log_cost_per_index_interval': [str(lo / n), str(hi / n)],
        'larger_clearing_factor': str(larger),
        'larger_clearing_has_identical_primitive_cost': True}


def main():
    sys.set_int_max_str_digits(200000)
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    cases = [check_coefficients(s, n, m)
             for s in (3, 5, 7, 9)
             for n in (0, 2, 4, 6, 8, 12, 20) for m in range(n + 1)]
    ledgers = [combined_ledger(s, n) for s in (3, 5, 7, 9)
               for n in (2, 4, 8, 12, 20) if n >= (s - 3) // 2]
    result = {
        'scope': 'Finite exact coefficient-denominator and gcd ledgers. '
                 'The general coefficient bound has a paper proof; no winning '
                 'all-index primitive-cost estimate or irrationality is asserted.',
        'coefficient_cases': cases,
        'coefficient_checks': sum(row['coefficient_checks'] for row in cases),
        'combined_ledgers': ledgers}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2), encoding='utf-8')
    print('cases', len(cases), 'coefficient checks', result['coefficient_checks'],
          'combined ledgers', len(ledgers), flush=True)


if __name__ == '__main__':
    main()
