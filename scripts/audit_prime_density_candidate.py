"""Falsification audit of explicit large-prime divisibility candidates."""

import argparse
import json
from math import gcd, lcm, prod
from pathlib import Path
import sys

from audit_primitive_normalization import weight_five_coordinates
from audit_smith_lattice import primes_to, valuation


def quantities(n, rows=None, gamma=None):
    if rows is None:
        clearing = lcm(*range(1, n+1))**5
        values = [[clearing*x for x in weight_five_coordinates(n, n-j)] for j in range(3)]
        assert all(x.denominator == 1 for row in values for x in row)
        rows = [list(map(int, row)) for row in values]
    x = [row[0] for row in rows]
    g = gcd(*x)
    if gamma is None:
        selected = [x[i]*rows[j][q]-x[j]*rows[i][q]
                    for i in range(3) for j in range(i+1, 3) for q in (1, 2)]
        numerator = gcd(*selected)
        assert divmod(numerator, g)[1] == 0
        gamma = numerator//g
    assert gamma > 0
    return g, gamma


def audit(n, g, gamma):
    boundary = prod(n-j for j in range(3))*prod(3*n-j for j in range(13))
    assert boundary > 0
    checked, failures = [], []
    for p in primes_to(3*n//2):
        if p*p <= 3*n+6 or divmod(boundary, p)[1] == 0:
            continue
        c = (3*n)//(2*p)-3*(n//(2*p))
        predicted_g = 3*int(p <= n)+int(c > 0)
        predicted_gamma = (2+c)*int(p <= n)
        actual_g, actual_gamma = valuation(g, p), valuation(gamma, p)
        row = {'prime': p, 'multinomial_valuation': c,
               'proposed_lower_column_bound': predicted_g,
               'actual_lower_column': actual_g,
               'proposed_image_content_bound': predicted_gamma,
               'actual_image_content': actual_gamma}
        checked.append(row)
        if actual_g < predicted_g or actual_gamma < predicted_gamma:
            failures.append(row)
    print(n, 'eligible primes', len(checked), 'counterexamples', len(failures), flush=True)
    return {'index': n, 'boundary_integer': str(boundary),
            'lower_column_gcd': str(g), 'kernel_image_content': str(gamma),
            'eligible_prime_cases': checked, 'counterexamples': failures}


def main():
    sys.set_int_max_str_digits(200000)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    source = json.loads((root/'notes/three-block-lattice-audit.json').read_text())['cases']
    data = []
    used = set()
    for row in source:
        n = row['index']
        if n < 6:
            continue
        rows = [[int(x) for x in r] for r in row['cleared_coordinate_rows']]
        g, gamma = quantities(n, rows, int(row['kernel_image_content']))
        data.append(audit(n, g, gamma))
        used.add(n)
    for n in (30, 50, 60, 100, 120, 180, 200, 240, 480):
        if n not in used:
            data.append(audit(n, *quantities(n)))
    result = {'scope': 'Finite tests of the paper-proved lower-column divisor '
                      'and falsification tests of an image-content candidate. The '
                      'latter fails at index 480, prime 47. No aggregate '
                      'image-content or final arithmetic estimate is asserted.',
              'large_prime_threshold': 'p^2 > 3n+6',
              'boundary_exclusion': 'p does not divide n(n-1)(n-2) product_(j=0..12)(3n-j)',
              'cases': sorted(data, key=lambda row: row['index'])}
    args.output.write_text(json.dumps(result, indent=2))
    print('Total prime cases:', sum(len(row['eligible_prime_cases']) for row in data),
          'counterexamples:', sum(len(row['counterexamples']) for row in data))


if __name__ == '__main__':
    main()
