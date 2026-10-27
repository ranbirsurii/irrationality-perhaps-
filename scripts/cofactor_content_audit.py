from fractions import Fraction as Q
from math import gcd, lcm, log
from pathlib import Path
import argparse
import json
import sys
from integer_determinants import adjugate_column
from joint_estimate_audit import H


def main():
    sys.set_int_max_str_digits(200000)
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    rows = []
    reference = json.loads(Path('notes/coefficient-chain-audit.json').read_text())['rows']
    for source in reference:
        s, size, shift = source['weight'], source['size'], source['shift']
        maximum = shift + 2 * size - 2
        scale = lcm(*range(1, maximum + 1)) ** s
        base = [[-scale * H(shift + i + j, s) for j in range(size)] for i in range(size)]
        assert all(x.denominator == 1 for row in base for x in row)
        base = [[int(x) for x in row] for row in base]
        difference = [base[0]] + [[base[i][j] - base[0][j] for j in range(size)]
                                   for i in range(1, size)]
        determinant, cofactors = adjugate_column(difference, 0)
        u, v = map(int, source['integer_boundary_row'])
        assert v == determinant == sum(base[0][j] * cofactors[j] for j in range(size))
        assert u == scale * sum(cofactors)
        content = gcd(*cofactors)
        g = gcd(u, v)
        assert content > 0 and g % content == 0
        primitive = [c // content for c in cofactors]
        assert gcd(*primitive) == 1
        rows.append({'weight': s, 'size': size, 'shift': shift,
                     'cofactor_content': str(content),
                     'remaining_content_after_cofactor_division': str(g // content),
                     'primitive_cofactor_vector': [str(c) for c in primitive],
                     'primitive_cofactor_sum': str(sum(primitive)),
                     'log_cofactor_content_per_size_squared': log(content) / size ** 2})
        print(s, size, 'cofactor saving/N^2', round(log(content) / size ** 2, 6),
              'residual gcd bits', (g // content).bit_length(), flush=True)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps({
        'scope': 'Exact cofactor identities and integral kernel certificates, not growth estimates.',
        'rows': rows}, indent=2), encoding='utf-8')


if __name__ == '__main__':
    main()
