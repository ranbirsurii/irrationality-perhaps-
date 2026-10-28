from pathlib import Path
import argparse
import json
import sympy as S
from sympy.polys.matrices import DomainMatrix


def generate(offset):
    n, t = S.symbols('n t')
    a = S.Poly(t**6 * (t + 2*n - offset + 1), t)
    b = S.Poly((t - n + offset - 1) * (t+n+6)**6, t)
    columns = [a*S.Poly((t+1)**k, t)-b*S.Poly(t**k, t) for k in range(31)]
    for ell in range(4):
        value = S.Poly(1, t)
        for i in range(1, 2*ell+1):
            value *= S.Poly(t-n+offset-i, t)
        for i in range(1, 4*ell+1):
            value *= S.Poly(t+2*n-offset+i, t)
        for i in range(2*ell+1, 7):
            value *= S.Poly((t+n+i)**6, t)
        columns.append(-value)
    matrix = DomainMatrix.from_Matrix(S.Matrix(
        [[c.nth(k) for c in columns] for k in range(37)]))
    print('solving offset', offset, flush=True)
    nullspace = matrix.nullspace()
    assert nullspace.shape[0] == 1
    _, primitive = nullspace.primitive()
    assert matrix.matmul(primitive.transpose()).is_zero_matrix
    vector = list(primitive.to_Matrix().row(0))
    if vector[-1].subs(n, 2) < 0:
        vector = [-x for x in vector]
    q = vector[-4:]
    raw = [S.expand(q[ell]*S.prod((n+i)**3 for i in range(2*ell+1, 7)))
           for ell in range(4)]
    common = S.gcd_list(raw)
    expected = S.prod((n+i)**3 for i in range(3-offset, 7))
    assert S.expand(common-expected) == 0
    p = [S.cancel(value/common) for value in raw]
    omega = 10**6*p[2]-10**9*p[3]-1000*p[1]+p[0]
    def coefficients(value):
        polynomial = S.Poly(S.expand(value), n)
        return [int(polynomial.nth(k)) for k in range(polynomial.degree()+1)]
    positive = [coefficients(value.subs(n, n+2))
                for value in (-p[0], p[1], p[2], p[3], omega)]
    assert all(cs[0] > 0 and all(c >= 0 for c in cs) for cs in positive)
    return {'offset': offset, 'step': 2, 'order': 3, 'cone_ratio': 1000, 'cone_start': 2,
            'q': list(map(coefficients, q)), 'x': list(map(coefficients, vector[:-4])),
            'p': list(map(coefficients, p)),
            'common_factor_shifts': list(range(3-offset, 7)), 'positive_shifted': positive}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--offset', type=int, choices=(0, 1), required=True)
    parser.add_argument('--output-dir', type=Path,
                        default=Path(__file__).resolve().parent.parent/'notes')
    args = parser.parse_args()
    data = generate(args.offset)
    args.output_dir.mkdir(parents=True, exist_ok=True)
    path = args.output_dir/f'pade-sign-recurrence-{args.offset}.json'
    path.write_text(json.dumps(data, indent=2), encoding='utf-8')
    print('wrote', path, flush=True)


if __name__ == '__main__':
    main()
