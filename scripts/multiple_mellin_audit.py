from fractions import Fraction as Q
from math import comb, factorial, gcd, lcm, log
from pathlib import Path
import argparse
import json
import sys
from joint_estimate_audit import H
from zeta_enclosure import euler_maclaurin_zeta_interval


def main():
    sys.set_int_max_str_digits(200000)
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    rows = []
    for s in (3, 5, 7, 9):
        for n in (1, 2, 3, 5, 10, 20, 30, 40):
            degree = s * n
            coefficients = [(-1) ** (degree - k) * comb(degree, k) * comb(n + k, n) ** s
                            for k in range(degree + 1)]
            a = sum(coefficients)
            assert a == factorial(degree) // factorial(n) ** s
            b = -sum(c * H(k, s) for k, c in enumerate(coefficients))
            d = b.denominator
            g = gcd(a * d, b.numerator)
            u, v = a * d // g, b.numerator // g
            order = 96
            while True:
                zlo, zhi = euler_maclaurin_zeta_interval(s, order)
                lo, hi = u * zlo + v, u * zhi + v
                if lo * hi > 0:
                    break
                order *= 2
                assert order <= 1536
            lower, upper = min(abs(lo), abs(hi)), max(abs(lo), abs(hi))
            row = {'weight': s, 'index': n, 'polynomial_degree': degree,
                   'target_coefficient': str(a), 'rational_constant': str(b),
                   'primitive_target_coefficient': str(u), 'primitive_constant': str(v),
                   'primitive_abs_interval': [str(lower), str(upper)],
                   'primitive_abs_gt_one': lower > 1,
                   'log_primitive_abs_per_index':
                       (log((lower + upper).numerator) - log((lower + upper).denominator) - log(2)) / n}
            rows.append(row)
            print(s, n, 'log primitive/n', round(row['log_primitive_abs_per_index'], 6),
                  'larger than one', lower > 1, flush=True)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps({
        'scope': 'Exact pure-target multiple-Mellin linear forms and rational zeta intervals; '
                 'finite results do not decide asymptotic smallness.',
        'rows': rows}, indent=2), encoding='utf-8')


if __name__ == '__main__':
    main()
