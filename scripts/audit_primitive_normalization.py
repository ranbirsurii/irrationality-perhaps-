"""Exact finite arithmetic audit, without an asymptotic conclusion."""

import argparse
from fractions import Fraction as Q
from functools import lru_cache
import json
from math import comb, factorial, gcd, lcm
from pathlib import Path
import sys

from analytic_sum_control import log_interval
from symmetric_pade_audit import poised_period_coordinates


def outward_interval(lo, hi, scale=10 ** 12):
    """Short rational endpoints, rounded outwards using integer arithmetic."""
    a, b = lo * scale, hi * scale
    lower = Q(a.numerator // a.denominator, scale)
    upper = Q(-((-b.numerator) // b.denominator), scale)
    assert lower <= lo <= hi <= upper
    return [str(lower), str(upper)]


@lru_cache(None)
def harmonics(n, k):
    values = [Q(0)]
    for j in range(1, n + 1):
        values.append(values[-1] + Q(1, j ** k))
    return tuple(values)


def weight_five_coordinates(n, m):
    """Normalized Laurent jets computed by logarithmic differentiation."""
    assert n >= 2 and not (n & 1) and 0 <= m <= n
    h = {k: harmonics(n + m, k) for k in range(1, 6)}
    totals, constant = [Q(0)] * 6, Q(0)
    d = lcm(*range(1, n + 1))
    for j in range(n + 1):
        leading = ((-1) ** (m + j) * comb(n, j) ** 5
                   * comb(j + m, m) * comb(n - j + m, m))
        log_jets = [Q(0)] + [
            (-1) ** (k - 1) * (
                (-1) ** k * h[k][j + m] + h[k][n - j + m]
                - 6 * ((-1) ** k * h[k][j] + h[k][n - j]))
            for k in range(1, 5)]
        jets = [Q(1)]
        for u in range(1, 5):
            jets.append(sum((log_jets[k] * jets[u - k]
                             for k in range(1, u + 1)), Q(0)) / u)
        for q in range(1, 6):
            coefficient = leading * jets[5 - q]
            assert (d ** (5 - q) * coefficient).denominator == 1
            totals[q] += coefficient
            constant -= coefficient * h[q][j]
    assert totals[1] == totals[2] == totals[4] == 0
    assert (d ** 5 * constant).denominator == 1
    return [totals[3], totals[5], constant]


def audit(n):
    rows = [weight_five_coordinates(n, m) for m in (n, n - 1)]
    crosschecked = n in (2, 4, 8, 12, 20)
    if crosschecked:
        for row, m in zip(rows, (n, n - 1)):
            scale = Q(factorial(n) ** 5, factorial(m) ** 2)
            assert row == [scale * x for x in poised_period_coordinates(2, n, m)]
    a0, a1 = (row[0] for row in rows)
    assert a0 * a1 < 0
    e = lcm(a0.denominator, a1.denominator)
    u0, u1 = int(e * a0), int(e * a1)
    weight_gcd = gcd(u0, u1)
    weights = [u1 // weight_gcd, -u0 // weight_gcd]
    if weights[0] < 0:
        weights = [-w for w in weights]
    assert all(w > 0 for w in weights) and gcd(*weights) == 1
    combined = [sum((w * row[k] for w, row in zip(weights, rows)), Q(0))
                for k in range(3)]
    assert combined[0] == 0
    mass = sum(weights)
    clearing = lcm(*range(1, n + 1)) ** 5
    cleared = [clearing * x for x in combined[1:]]
    assert all(x.denominator == 1 for x in cleared)
    a, b = map(int, cleared)
    content = gcd(a, b)
    assert content > 0
    cost = Q(clearing * mass, content)

    # Independent normalization: start with the rational, mass-one pair,
    # compute its least denominator, then remove its own integer content.
    normalized = [x / mass for x in combined[1:]]
    least_denominator = lcm(*(x.denominator for x in normalized))
    minimal_pair = [int(least_denominator * x) for x in normalized]
    minimal_content = gcd(*minimal_pair)
    assert minimal_content > 0
    independent_cost = Q(least_denominator, minimal_content)
    assert cost == independent_cost
    primitive = [a // content, b // content]
    assert primitive == [x // minimal_content for x in minimal_pair]
    assert gcd(*primitive) == 1
    assert all(cost * x == y for x, y in zip(normalized, primitive))

    # Every kernel term is positive after k=m. Its first positive term
    # gives a rigorous lower bound without evaluating any zeta value.
    first_terms = [Q(factorial(n) ** 5 * factorial(m) ** 4
                     * factorial(n + 2 * m + 1),
                     factorial(n + m + 1) ** 6) for m in (n, n - 1)]
    primitive_lower = cost * min(first_terms)
    plo, phi = log_interval(primitive_lower)

    old = json.loads((Path(__file__).resolve().parents[1]
                     / 'notes/pade-arithmetic-budget.json').read_text(encoding='utf-8'))
    old_rows = [row for row in old['combined_ledgers']
                if row['weight'] == 5 and row['index'] == n]
    if old_rows:
        assert len(old_rows) == 1
        assert cost == Q(old_rows[0]['exact_primitive_cost'])
    loglo, loghi = log_interval(cost)
    ratio = Q(content, mass)
    rlo, rhi = log_interval(ratio)
    print(n, 'log(K)/n', float((loglo + loghi) / (2 * n)),
          'log(h/M)/n', float((rlo + rhi) / (2 * n)),
          'primitive form > 1:', primitive_lower > 1, flush=True)
    return {
        'index': n,
        'weights': list(map(str, weights)),
        'weight_mass': str(mass),
        'clearing_factor': str(clearing),
        'full_gcd': str(content),
        'primitive_coefficients': list(map(str, primitive)),
        'exact_multiplier': str(cost),
        'independent_least_denominator': str(least_denominator),
        'independent_content': str(minimal_content),
        'independent_normalizations_agree': True,
        'laurent_convolution_crosschecked': crosschecked,
        'exact_primitive_form_lower_bound': str(primitive_lower),
        'primitive_form_lower_bound_exceeds_one': primitive_lower > 1,
        'log_primitive_form_lower_bound_per_index_interval':
            outward_interval(plo / n, phi / n),
        'log_multiplier_per_index_interval': outward_interval(loglo / n, loghi / n),
        'log_gcd_to_mass_per_index_interval': outward_interval(rlo / n, rhi / n)}


def main():
    sys.set_int_max_str_digits(200000)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    rows = [audit(n) for n in (2, 4, 8, 12, 20, 40, 80, 160)]
    result = {
        'scope': 'Finite exact normalization audit. Neither an asymptotic '
                 'arithmetic estimate nor an irrationality proof.',
        'cases': rows}
    args.output.write_text(json.dumps(result, indent=2), encoding='utf-8')


if __name__ == '__main__':
    main()
