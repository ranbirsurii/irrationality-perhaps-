from fractions import Fraction as Q
from math import gcd, lcm, log, prod
from pathlib import Path
import argparse
import json
from joint_estimate_audit import audit, zeta_interval
from sparse_hankel_audit import coefficients


def primes_up_to(m):
    return [p for p in range(2, m + 1)
            if all(p % d for d in range(2, int(p ** 0.5) + 1))]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    rows = []
    for s in (3, 5, 7, 9):
        interval = zeta_interval(s, 600)
        for size in (5, 10, 20):
            m = 2 * size - 2
            scale = lcm(*range(1, m + 1)) ** (s * size)
            a, b = coefficients(s, tuple(range(size)))
            u, v = a * scale, b * scale
            assert u.denominator == v.denominator == 1
            u, v = int(u), int(v)
            g = gcd(abs(u), abs(v))
            row_cost = prod(lcm(*range(1, i + size)) ** s for i in range(size))
            assert scale % row_cost == 0
            row_saving = scale // row_cost
            assert g % row_saving == 0
            row_a, row_b = a * row_cost, b * row_cost
            assert row_a.denominator == row_b.denominator == 1
            assert gcd(abs(int(row_a)), abs(int(row_b))) == g // row_saving
            residual = g
            weights = {}
            for p in primes_up_to(m):
                e = 0
                while residual % p == 0:
                    residual //= p
                    e += 1
                if e:
                    weights[str(p)] = e
            extra_weights = {}
            for p in primes_up_to(1000):
                if p <= m:
                    continue
                e = 0
                while residual % p == 0:
                    residual //= p
                    e += 1
                if e:
                    extra_weights[str(p)] = e
            form = audit(a, b, *interval, size * size)
            assert Q(form['primitive_a']) == u // g
            assert Q(form['primitive_b']) == v // g
            assert g * int(form['primitive_a']) == u
            assert g * int(form['primitive_b']) == v
            row = {'weight': s, 'size': size, 'shift': 0,
                   'integer_boundary_row': [str(u), str(v)],
                   'content': str(g), 'prime_torsion_lengths_up_to_m': weights,
                   'rowwise_cost': str(row_cost),
                   'guaranteed_rowwise_saving': str(row_saving),
                   'remaining_content_after_rowwise_saving': str(g // row_saving),
                   'prime_torsion_lengths_above_m_up_to_1000': extra_weights,
                   'remaining_content_with_no_prime_factor_up_to_1000': str(residual),
                   'uniform_cost_per_size_squared': log(scale) / size ** 2,
                   'torsion_saving_per_size_squared': log(g) / size ** 2,
                   'rowwise_cost_per_size_squared': log(row_cost) / size ** 2,
                   'guaranteed_rowwise_saving_per_size_squared': log(row_saving) / size ** 2,
                   'form': form}
            rows.append(row)
            print(s, size, 'cost', round(row['uniform_cost_per_size_squared'], 6),
                  'saving', round(row['torsion_saving_per_size_squared'], 6),
                  'primitive decay', round(form['primitive_decay_exponent'], 6),
                  'rowwise cost', round(log(row_cost) / size ** 2, 6),
                  'extra prime lengths', extra_weights, 'residual content', residual)
    result = {'scope': 'Exact integer coefficient complexes and finite rational interval checks; '
                        'displayed logarithms are approximate. No geometric realization is assumed.',
              'rows': rows}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2), encoding='utf-8')


if __name__ == '__main__':
    main()
