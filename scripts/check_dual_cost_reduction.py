"""Exact dual-form reduction of existing records; no new family indices."""

from fractions import Fraction
from hashlib import sha256
import json
from math import gcd
from pathlib import Path
import sys


def dot(x, y):
    return sum(a * b for a, b in zip(x, y))


def reduce_binary_form(A, B, C):
    assert A > 0 and A * C > B * B
    original = (A, B, C)
    U = [[1, 0], [0, 1]]
    steps = 0
    while True:
        if C < A:
            A, C = C, A
            U = [[row[1], row[0]] for row in U]
        q = (2 * B + A) // (2 * A)
        if q == 0:
            break
        C, B = C - 2 * q * B + q * q * A, B - q * A
        U = [[row[0], row[1] - q * row[0]] for row in U]
        steps += 1
    assert A <= C and 2 * abs(B) <= A
    assert abs(U[0][0] * U[1][1] - U[0][1] * U[1][0]) == 1
    A0, B0, C0 = original

    def pairing(x, y):
        return A0 * x[0] * y[0] + B0 * (x[0] * y[1] + x[1] * y[0]) + C0 * x[1] * y[1]

    u, v = [row[0] for row in U], [row[1] for row in U]
    assert (pairing(u, u), pairing(u, v), pairing(v, v)) == (A, B, C)
    return (A, B, C), U, steps


def analyze(row):
    a, b = ([int(x) for x in v] for v in row['saturated_gauss_basis'])
    data = [[int(x) for x in v] for v in row['cleared_coordinate_rows']]
    A, B, C = dot(a, a), dot(a, b), dot(b, b)
    assert 0 < A <= C and 2 * abs(B) <= A
    x = [v[0] for v in data]
    assert dot(x, a) == dot(x, b) == 0
    normal = [v // gcd(*x) for v in x]
    exterior = [a[1] * b[2] - a[2] * b[1],
                a[2] * b[0] - a[0] * b[2],
                a[0] * b[1] - a[1] * b[0]]
    assert exterior in (normal, [-v for v in normal])
    y, z = [v[1] for v in data], [v[2] for v in data]
    ya, yb, za, zb = dot(a, y), dot(b, y), dot(a, z), dot(b, z)
    H2, delta = A * C - B * B, ya * zb - yb * za
    S11 = C * ya * ya - 2 * B * ya * yb + A * yb * yb
    S12 = C * ya * za - B * (ya * zb + yb * za) + A * yb * zb
    S22 = C * za * za - 2 * B * za * zb + A * zb * zb
    assert S11 * S22 - S12 * S12 == delta * delta * H2
    reduced, U, steps = reduce_binary_form(S11, S12, S22)
    mu, beta, nu = reduced
    assert mu * nu - beta * beta == delta * delta * H2

    c0 = [zb * x - za * t for x, t in zip(a, b)]
    c1 = [ya * t - yb * x for x, t in zip(a, b)]
    primal = (dot(c0, c0), dot(c0, c1), dot(c1, c1))
    assert primal == (S22, -S12, S11)
    primal_reduced, _, _ = reduce_binary_form(*primal)
    assert (primal_reduced[0], primal_reduced[2]) == (mu, nu)
    eta = gcd(S11, 2 * S12, S22)
    gamma = int(row['kernel_image_content'])
    assert gamma == gcd(ya, yb, za, zb)
    assert eta > 0 and divmod(eta, gamma * gamma)[1] == 0
    optimal_square = Fraction(nu, delta * delta)
    common_square = Fraction(C, gamma * gamma)
    coarse_dual_square = Fraction(4 * H2, 3 * eta)
    assert optimal_square < common_square < coarse_dual_square
    return {
        'index': row['index'], 'gauss_steps': steps,
        'dual_integral_gram': list(map(str, (S11, S12, S22))),
        'reduced_gram': list(map(str, reduced)),
        'unimodular_reduction_witness': [list(map(str, v)) for v in U],
        'original_gram_determinant': str(H2), 'coefficient_determinant': str(delta),
        'optimal_primitive_pair_Euclidean_normalization_cost_squared': str(optimal_square),
        'optimal_pair_strictly_improves_common_content': True,
        'coarse_gcd_dual_bound_is_strictly_weaker': True,
        'ambient_primal_and_dual_gram_checks_agree': True,
        'scope': 'Exact existing record only; no asymptotic inference.'
    }


def main():
    sys.set_int_max_str_digits(200000)
    root = Path(__file__).resolve().parents[1]
    source = root / 'notes/three-block-lattice-audit.json'
    cases = json.loads(source.read_text(encoding='utf-8'))['cases']
    result = {
        'scope': 'Reuses stored weight-five indices 20,80,1280; does not recompute coefficients or prove a limiting rate.',
        'source_sha256': sha256(source.read_bytes()).hexdigest(),
        'cases': [analyze(row) for row in cases if row['index'] in (20, 80, 1280)]
    }
    assert len(result['cases']) == 3
    output = root / 'notes/dual-cost-reduction-checks.json'
    output.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    for row in result['cases']:
        print(json.dumps({key: row[key] for key in (
            'index', 'gauss_steps', 'optimal_pair_strictly_improves_common_content',
            'coarse_gcd_dual_bound_is_strictly_weaker', 'scope')}))


if __name__ == '__main__':
    main()
