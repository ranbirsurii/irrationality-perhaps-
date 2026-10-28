"""Exact requested checks of the actual weight-seven cancellation profile."""

from fractions import Fraction as Q
from functools import lru_cache
from itertools import combinations
from math import comb, factorial, gcd, lcm
from pathlib import Path
import json
import sys

from analytic_sum_control import log_interval
from symmetric_pade_audit import poised_period_coordinates, one_dimensional_nullvector
from zeta_enclosure import euler_maclaurin_zeta_interval


@lru_cache(None)
def harmonic(n, q):
    return sum((Q(1, k ** q) for k in range(1, n + 1)), Q(0))


def normalized_log_jet_coordinates(s, n, m):
    total = [Q(0)] * (s + 1)
    constant = Q(0)
    for j in range(n + 1):
        leading = ((-1) ** (m + j) * comb(n, j) ** s
                   * comb(j + m, m) * comb(n - j + m, m))
        log_jet = [Q(0)] + [
            (-1) ** (q - 1) * (
                (-1) ** q * harmonic(j + m, q)
                + harmonic(n - j + m, q)
                - (s + 1) * ((-1) ** q * harmonic(j, q)
                             + harmonic(n - j, q)))
            for q in range(1, s)]
        jet = [Q(1)]
        for u in range(1, s):
            jet.append(sum((log_jet[q] * jet[u - q]
                            for q in range(1, u + 1)), Q(0)) / u)
        for q in range(1, s + 1):
            coefficient = leading * jet[s - q]
            total[q] += coefficient
            constant -= coefficient * harmonic(j, q)
    assert total[1] == 0
    assert all(total[q] == 0 for q in range(2, s + 1, 2))
    return [total[q] for q in range(3, s + 1, 2)] + [constant]


def det(rows):
    if not rows:
        return 1
    return sum((-1) ** j * rows[0][j] *
               det([row[:j] + row[j + 1:] for row in rows[1:]])
               for j in range(len(rows)))


def maximal_content(rows):
    return gcd(*(det([[row[j] for j in cols] for row in rows])
                 for cols in combinations(range(len(rows[0])), len(rows))))


def check(n):
    r, s = 3, 7
    d = lcm(*range(1, n + 1))
    clearing = d ** s
    coordinates = []
    for j in range(r + 1):
        m = n - j
        first = normalized_log_jet_coordinates(s, n, m)
        scale = Q(factorial(n) ** s, factorial(m) ** 2)
        second = [scale * value for value in poised_period_coordinates(r, n, m)]
        assert first == second
        coordinates.append(first)
    rational_rows = [list(row) for row in zip(*coordinates)]
    cleared = [[clearing * value for value in row] for row in rational_rows]
    assert all(value.denominator == 1 for row in cleared for value in row)
    lower = [list(map(int, row)) for row in cleared[:2]]
    target, constant = [list(map(int, row)) for row in cleared[2:]]
    delta = maximal_content(lower)
    assert delta > 0
    gamma = gcd(maximal_content(lower + [target]),
                maximal_content(lower + [constant])) // delta
    assert gamma > 0
    candidates = []
    for support in combinations(range(4), 3):
        submatrix = [[Q(row[j]) for j in support] for row in lower]
        w = one_dimensional_nullvector(submatrix, 3)
        if all(value <= 0 for value in w):
            w = [-value for value in w]
        if not all(value >= 0 for value in w):
            continue
        full = [0] * 4
        for j, value in zip(support, w):
            full[j] = value
        assert all(sum(x * y for x, y in zip(row, full)) == 0 for row in lower)
        a = sum(x * y for x, y in zip(target, full))
        b = sum(x * y for x, y in zip(constant, full))
        h = gcd(a, b)
        assert h > 0 and h == gamma * (h // gamma)
        a, b = a // h, b // h
        order = 96
        while True:
            zl, zh = euler_maclaurin_zeta_interval(s, order)
            lo, hi = sorted((a * zl + b, a * zh + b))
            if lo > 0:
                break
            order *= 2
            assert order <= 1536
        mass = sum(full)
        cost = Q(clearing * mass, h)
        candidates.append({
            'weights': list(map(str, full)), 'mass': str(mass),
            'content_for_vector': str(h), 'lattice_image_content': str(gamma),
            'mass_over_image_content': str(Q(mass, gamma)),
            'primitive_clearing_cost': str(cost),
            'primitive_target': str(a), 'primitive_constant': str(b),
            'primitive_form_positive': True,
            'primitive_form_below_one': hi < 1,
            'primitive_form_interval': [str(lo), str(hi)]})
    assert candidates
    assert len(candidates) >= 2
    wa, wb = [list(map(int, entry['weights'])) for entry in candidates[:2]]
    ya = sum(x * y for x, y in zip(target, wa))
    yb = sum(x * y for x, y in zip(target, wb))
    za = sum(x * y for x, y in zip(constant, wa))
    zb = sum(x * y for x, y in zip(constant, wb))
    delta = ya * zb - yb * za
    assert delta != 0
    u = [ya * x - yb * y for x, y in zip(wb, wa)]
    assert all(sum(x * y for x, y in zip(row, u)) == 0 for row in lower)
    assert sum(x * y for x, y in zip(target, u)) == 0
    assert sum(x * y for x, y in zip(constant, u)) == delta
    quotient = Q(delta, gamma ** 2)
    assert quotient.denominator == 1
    best = min(candidates, key=lambda c: Q(c['primitive_clearing_cost']))
    cost_rate = log_interval(Q(best['mass_over_image_content']))
    return {'weight': s, 'even_index': n,
            'block_lengths': list(range(n, n - 4, -1)),
            'independent_coefficient_algorithms_agree': True,
            'cleared_lower_period_rows': [list(map(str, row)) for row in lower],
            'positive_circuit_count': len(candidates),
            'target_eliminating_vector': list(map(str, u)),
            'target_free_constant': str(delta),
            'target_free_constant_over_content_squared': str(quotient),
            'target_free_constant_is_nonzero_integer': True,
            'best_of_checked_positive_circuits': best,
            'observed_log_relative_cost_per_index':
                [float(value / n) for value in cost_rate],
            'scope': 'Exact specified indices only; no asymptotic inference.'}


def main():
    sys.set_int_max_str_digits(200000)
    results = [check(n) for n in (6, 8)]
    destination = Path('publication/high-weight-criterion/integral-cancellation-checks.json')
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(results, indent=2) + '\n', encoding='utf-8')
    source = ['import Mathlib.Tactic.NormNum', '']
    for result in results:
        n = result['even_index']
        w = result['best_of_checked_positive_circuits']['weights']
        for row_index, row in enumerate(result['cleared_lower_period_rows']):
            expression = ' + '.join(f'({x}) * ({y})' for x, y in zip(row, w))
            source += [f'theorem weightSeven_index{n}_lower{row_index}_cancels :',
                       f'    ({expression} : Int) = 0 := by norm_num', '']
    Path('publication/high-weight-criterion/IntegralCancellationExamples.lean').write_text(
        '\n'.join(source), encoding='utf-8')
    for result in results:
        print('n', result['even_index'], 'positive circuits', result['positive_circuit_count'],
              'coefficient algorithms agree',
              result['independent_coefficient_algorithms_agree'],
              'relative cost log/n', result['observed_log_relative_cost_per_index'],
              'primitive form below one',
              result['best_of_checked_positive_circuits']['primitive_form_below_one'])


if __name__ == '__main__':
    main()
