from fractions import Fraction as Q
from math import factorial, prod
from pathlib import Path
import argparse
import json
import sys
from joint_estimate_audit import audit, zeta_interval
from sparse_hankel_audit import coefficients


def jacobi_bound(r, n, shift):
    return Q(factorial(2 * r - 1),
             prod(range(n, n + 2 * r)) * prod(range(n + shift, n + shift + 2 * r)))


def main():
    sys.set_int_max_str_digits(20000)
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    rows = []
    for s in (3, 5, 7, 9):
        r = (s - 1) // 2
        interval = zeta_interval(s, 600)
        for n in (5, 10, 20):
            for shift in (0, n):
                a, b = coefficients(s, tuple(range(n)), shift)
                error_lo, error_hi = interval[0] + b / a, interval[1] + b / a
                lower = jacobi_bound(r, n, shift)
                upper = jacobi_bound(r, n - r, shift)
                assert 0 < lower <= error_lo <= error_hi <= upper
                form = audit(a, b, *interval, n * n)
                primitive_u = int(form['primitive_a'])
                height_scale = n ** (2 * r) * (n + shift) ** (2 * r)
                assert Q(form['primitive_abs_lower']) == primitive_u * error_lo
                assert Q(form['primitive_abs_upper']) == primitive_u * error_hi
                row = {'weight': s, 'size': n, 'shift': shift,
                       'jacobi_lower': str(lower), 'jacobi_upper': str(upper),
                       'error_interval': [str(error_lo), str(error_hi)],
                       'primitive_target_coefficient': str(primitive_u),
                       'height_scale': str(height_scale),
                       'scaled_primitive_height': str(Q(primitive_u, height_scale)),
                       'scaled_error_interval': [str(error_lo * height_scale),
                                                 str(error_hi * height_scale)],
                       'primitive_abs_gt_one': form['primitive_abs_gt_one']}
                rows.append(row)
                print(s, n, shift, 'error', float((error_lo + error_hi) / 2),
                      'scaled error', float((error_lo + error_hi) * height_scale / 2),
                      'primitive form greater than one', form['primitive_abs_gt_one'])
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps({
        'scope': 'Exact rational interval checks of the proved endpoint sandwich; '
                 'the primitive height condition is not inferred from finite data.',
        'rows': rows}, indent=2), encoding='utf-8')


if __name__ == '__main__':
    main()
