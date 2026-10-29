"""Exact weighted infinity-to-one transition norms, without asymptotic extrapolation."""
from fractions import Fraction as Q
from math import factorial, lcm
from pathlib import Path
import json

from check_integral_cancellation import normalized_log_jet_coordinates
from integer_determinants import adjugate_column
from weight_seven_combined_kernel import multiply


def weighted_profile(r, n, vector, numerator_length=None):
    length=n if numerator_length is None else numerator_length
    assert r<=length<=n
    out = [Q(0)] * (r + 1)
    for j, value in enumerate(vector):
        polynomial = [Q(1)]
        for h in range(length-r+1, length-j+1):
            polynomial = multiply(polynomial, [-h*(n+h), 1])
        scale = value * Q(factorial(length-r)**2, factorial(length-j)**2)
        for ell, coefficient in enumerate(polynomial):
            out[ell] += scale * coefficient * (12*n*n)**ell
    return out


def mass(vector):
    return sum(map(abs, vector), Q(0))


def main():
    root = Path(__file__).resolve().parents[1]
    source = json.loads((root/'notes/isolated-derivative-family.json').read_text())
    old = json.loads((root/'notes/cross-family-transition.json').read_text())['cases']
    cache = {}
    records = []
    for case, previous in zip(source['cases'], old, strict=True):
        s, n = case['weight'], case['index']
        r = (s-1)//2
        key = s, n
        if key not in cache:
            D = lcm(*range(1, n+1))**s
            blocks = [normalized_log_jet_coordinates(s, n, n-j) for j in range(r+1)]
            rational_matrix = [[D*x for x in row] for row in zip(*blocks)]
            assert all(x.denominator == 1 for row in rational_matrix for x in row)
            matrix = [list(map(int, row)) for row in rational_matrix]
            delta, a = adjugate_column(matrix, r-1)
            again, b = adjugate_column(matrix, r)
            assert delta == again and delta != 0
            u = weighted_profile(r, n, [Q(x, delta) for x in a])
            v = weighted_profile(r, n, [Q(x, delta) for x in b])
            plus = mass([x+y for x, y in zip(u, v)])
            minus = mass([x-y for x, y in zip(u, v)])
            exact = max(plus, minus)
            triangle = mass(u)+mass(v)
            assert max(mass(u), mass(v)) <= exact <= triangle <= 2*exact
            breakpoints = sorted({-x/y for x, y in zip(u, v) if y})
            assert breakpoints
            minimum = min(mass([x+t*y for x, y in zip(u, v)]) for t in breakpoints)
            assert minimum > 0
            cache[key] = u, v, exact, triangle, minimum
        u, v, exact, triangle, minimum = cache[key]
        a, b = map(int, case['primitive_coefficients'])
        actual = mass([a*x+b*y for x, y in zip(u, v)])
        assert actual == Q(previous['original_family_weighted_profile_height'])
        assert actual <= exact*max(abs(a), abs(b))
        assert abs(a)*minimum <= actual
        for p, q in ((Q(1), Q(1)), (Q(1), Q(-1)), (Q(2,3), Q(-4,5)), (Q(0), Q(1))):
            assert mass([p*x+q*y for x, y in zip(u, v)]) <= exact*max(abs(p), abs(q))
        records.append({'weight': s, 'index': n, 'zero_length': case['zero_length'],
                        'exact_operator_norm': str(exact),
                        'triangle_envelope': str(triangle),
                        'exact_height': str(actual),
                        'target_pair_maximum': str(max(abs(a), abs(b))),
                        'operator_majorant': str(exact*max(abs(a), abs(b))),
                        'continuous_direction_minimum': str(minimum),
                        'directional_lower_certificate': str(abs(a)*minimum),
                        'triangle_to_optimal_factor': str(triangle/exact)})
    (root/'notes/exact-transition-norm.json').write_text(json.dumps({
        'cases': records, 'uniform_rate_proved': False,
        'scope': 'Exact rational operator norms and finite checks; no growth extrapolation.'}, indent=2))
    print(len(records), 'exact operator checks passed across', len(cache), 'matrices')


if __name__ == '__main__':
    main()
