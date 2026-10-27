from fractions import Fraction as Q
from math import gcd, lcm, log, prod
from pathlib import Path
import argparse
import json
import sys
from integer_determinants import bareiss


def rowwise_coefficients(s, size, shift):
    maximum = shift + 2 * size - 2
    harmonic = [Q(0)]
    for k in range(1, maximum + 1):
        harmonic.append(harmonic[-1] + Q(1, k ** s))
    scales = [lcm(*range(1, shift + i + size)) ** s for i in range(size)]
    constant = []
    for i, scale in enumerate(scales):
        row = [-scale * harmonic[shift + i + j] for j in range(size)]
        assert all(v.denominator == 1 for v in row)
        constant.append([int(v) for v in row])
    b = bareiss(constant)
    a = bareiss([[value + scale for value in row]
                 for row, scale in zip(constant, scales)]) - b
    assert a > 0
    return a, b, prod(scales)


def main():
    sys.set_int_max_str_digits(200000)
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    reference = json.loads(Path('notes/coefficient-chain-audit.json').read_text())['rows']
    for row in reference:
        a, b, d = rowwise_coefficients(row['weight'], row['size'], row['shift'])
        assert d == int(row['rowwise_cost'])
        saving = int(row['guaranteed_rowwise_saving'])
        assert a * saving == int(row['integer_boundary_row'][0])
        assert b * saving == int(row['integer_boundary_row'][1])
    print('Bareiss coefficient construction agrees with all 12 stored rational audits.', flush=True)
    rows = []
    for s in (3, 5, 7, 9):
        for size in (30, 40, 60):
            a, b, d = rowwise_coefficients(s, size, 0)
            content = gcd(abs(a), abs(b))
            u, v = a // content, b // content
            scale = size ** (2 * (s - 1))
            excess_bits = (u // scale).bit_length() - 1
            assert excess_bits >= 0 and u >= scale * 2 ** excess_bits
            row = {'weight': s, 'size': size, 'shift': 0,
                   'primitive_target_coefficient': str(u),
                   'primitive_constant_coefficient': str(v),
                   'rowwise_cost': str(d), 'remaining_content': str(content),
                   'height_scale': str(scale), 'certified_height_excess_bits': excess_bits,
                   'log_target_coefficient_per_size_squared': log(u) / size ** 2,
                   'log_remaining_content_per_size_squared': log(content) / size ** 2}
            rows.append(row)
            print(s, size, 'log(u)/N^2', round(log(u) / size ** 2, 6),
                  'remaining gcd log/N^2', round(log(content) / size ** 2, 6),
                  'u >= scale times 2^', excess_bits, flush=True)
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(json.dumps({
                'scope': 'Exact coefficients and finite height lower certificates, '
                         'not an asymptotic impossibility theorem.',
                'rows': rows}, indent=2), encoding='utf-8')


if __name__ == '__main__':
    main()
