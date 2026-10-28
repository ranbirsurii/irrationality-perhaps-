"""Verify the uniform block-length recurrence and its positive reduction."""

import argparse
from fractions import Fraction as Q
import json
from math import prod
from pathlib import Path

from audit_primitive_normalization import weight_five_coordinates


def add(a, b, scale=1):
    result = a.copy()
    for key, value in b.items():
        result[key] = result.get(key, 0)+scale*value
        if result[key] == 0:
            del result[key]
    return result


def mul(a, b):
    result = {}
    for i, x in a.items():
        for j, y in b.items():
            key = tuple(v+w for v, w in zip(i, j))
            result[key] = result.get(key, 0)+x*y
    return {key: value for key, value in result.items() if value}


def power(a, exponent):
    result = {(0, 0, 0): 1}
    for _ in range(exponent):
        result = mul(result, a)
    return result


def scale(a, c):
    return {key: value*c for key, value in a.items() if value*c}


def evaluate(a, n, m, t=0):
    return sum(c*n**i*m**j*t**k for (i, j, k), c in a.items())


def verify():
    one = {(0, 0, 0): 1}
    n, m, t = ({(1, 0, 0): 1}, {(0, 1, 0): 1}, {(0, 0, 1): 1})
    m1 = add(m, one)
    nodes = [mul(add(m, scale(one, i)), add(add(n, m), scale(one, i)))
             for i in (1, 2, 3)]
    a1 = mul(power(n, 4), add(scale(m1, 6), n, -1))
    a2 = mul(power(n, 2), add(scale(m1, 9), scale(n, 5), -1))
    a3 = add(scale(m1, 2), scale(n, 5), -1)
    q0 = mul(power(m1, 6), add(n, scale(m1, 2)))
    q1 = add(add(a1, mul(a2, add(nodes[0], nodes[1]))), mul(a3,
        add(add(power(nodes[0], 2), mul(nodes[0], nodes[1])), power(nodes[1], 2))))
    q2 = add(a2, mul(a3, add(add(nodes[0], nodes[1]), nodes[2])))
    qs = [q0, q1, q2, a3]
    u = mul(t, add(t, n))
    left = add(mul(power(t, 6), add(add(t, n), m1)),
               mul(add(t, m1, -1), power(add(t, n), 6)), -1)
    basis, right = one, {}
    for i, q in enumerate(qs):
        right = add(right, mul(q, basis))
        if i < 3:
            basis = mul(basis, add(u, nodes[i], -1))
    assert left == right, 'universal identity in Z[n,m,t]'

    # Substitute n=m+3+r; the third formal variable now denotes r.
    positive = []
    for index, q in enumerate(qs):
        shifted = {}
        for (i, j, k), c in q.items():
            assert k == 0
            term = mul(power(add(add(m, t), scale(one, 3)), i), power(m, j))
            shifted = add(shifted, term, c)
        sign = 1 if index == 0 else -1
        assert shifted and all(sign*c > 0 for c in shifted.values())
        assert sign*shifted.get((0, 0, 0), 0) > 0
        positive.append({'index': index, 'sign': sign, 'shifted_term_count': len(shifted)})

    checks = []
    for nn in (4, 8, 12, 20, 40):
        for mm in sorted({0, (nn-3)//2, nn-3}):
            q = [evaluate(poly, nn, mm) for poly in qs]
            factors = [prod((mm+i)**2 for i in range(1, ell+1)) for ell in range(4)]
            vectors = [weight_five_coordinates(nn, mm+ell) for ell in range(4)]
            assert all(sum(q[ell]*factors[ell]*vectors[ell][j] for ell in range(4)) == 0
                       for j in range(3))
            assert q[0] > 0 and all(value < 0 for value in q[1:])
            checks.append({'index': nn, 'length': mm, 'recurrence_coefficients':
                           [str(q[ell]*factors[ell]) for ell in range(4)]})
    return {'scope': 'Universal polynomial identity and coefficient-sign proof; '
                     'paper boundary argument yields the full period-vector recurrence. '
                     'No limiting primitive-cost estimate.',
            'polynomial_identity_verified': True, 'uniform_signs': positive,
            'period_coordinate_checks': checks,
            'positive_cone_generators': ['length n', 'length n-1', 'length n-2']}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    data = verify()
    args.output.write_text(json.dumps(data, indent=2))
    print('Universal block recurrence and sign certificates verified;',
          len(data['period_coordinate_checks']), 'exact coordinate cases.')


if __name__ == '__main__':
    main()
