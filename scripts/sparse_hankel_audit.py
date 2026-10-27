from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
import argparse
import json
from joint_estimate_audit import H, determinant, audit, zeta_interval


def coefficients(s, exponents, shift=0):
    base = [[-H(shift + i + j, s) for j in exponents] for i in exponents]
    b = determinant(base)
    a = determinant([[1 + x for x in row] for row in base]) - b
    assert a > 0
    return a, b


def check(s, exponents, interval, shift=0):
    a, b = coefficients(s, exponents, shift)
    result = audit(a, b, *interval, len(exponents) ** 2)
    assert a * interval[0] + b > 0
    return {'weight': s, 'exponents': list(exponents), 'shift': shift, **result}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    rows, families = [], []
    for s in (3, 5, 7, 9):
        interval = zeta_interval(s, 600)
        best = None
        for size in (2, 3, 4):
            for rest in combinations(range(1, 11), size - 1):
                row = check(s, (0, *rest), interval)
                rows.append(row)
                if best is None or Q(row['primitive_abs_upper']) < Q(best['primitive_abs_upper']):
                    best = row
        print('Finite best', s, best['exponents'],
              best['primitive_decay_exponent'])
        for size in (4, 6, 8):
            patterns = {
                'consecutive': tuple(range(size)),
                'even': tuple(2 * j for j in range(size)),
                'quadratic': tuple(j * j for j in range(size)),
                'gapped': tuple(j + j // 2 for j in range(size)),
                'two_clusters': tuple(j if j < size // 2 else j + size for j in range(size)),
            }
            for name, exponents in patterns.items():
                row = check(s, exponents, interval)
                families.append({'family': name, **row})
            print('Family size', s, size,
                  [(r['family'], round(r['primitive_decay_exponent'], 6))
                   for r in families if r['weight'] == s and len(r['exponents']) == size])
    result = {'scope': 'Finite exact rational interval checks, not asymptotic estimates.',
              'weights': [3, 5, 7, 9], 'Euler_transform_terms': 600,
              'small_space_search': rows, 'family_checks': families}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2), encoding='utf-8')


if __name__ == '__main__':
    main()
