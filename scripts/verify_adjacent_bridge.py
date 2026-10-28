"""Verify the universal adjacent-family certificate and finite period checks."""

import argparse
from fractions import Fraction as Q
import json
from math import comb, factorial, prod
from pathlib import Path

from audit_primitive_normalization import weight_five_coordinates
from audit_smith_lattice import determinant, matmul, valuation
from verify_sign_recurrences import add, ev, linear, mul, power, univariate


PAIRS = ((0, 1), (0, 2), (1, 2))


def compound(a):
    return [[a[i][k]*a[j][l]-a[i][l]*a[j][k]
             for k, l in PAIRS] for i, j in PAIRS]


def coordinate(n, offset):
    return [x / (n*n if offset else 1)
            for x in weight_five_coordinates(n, n-offset)]


def state(n):
    return [coordinate(n+2*ell, 0) for ell in range(3)]


def verify(root):
    data = json.loads((root/'notes/adjacent-family-bridge.json').read_text())
    assert data['depth'] == 2 and len(data['x']) == 21 and len(data['q']) == 4
    one, t, t1 = linear(c=1), linear(b=1), linear(b=1, c=1)
    u = mul(power(t, 6), linear(a=2, b=1))
    v = mul(linear(a=-1, b=1), power(linear(a=1, b=1, c=4), 6))
    x, shifted = {}, {}
    for k, cs in enumerate(data['x']):
        x = add(x, mul(univariate(cs), power(t, k)))
        shifted = add(shifted, mul(univariate(cs), power(t1, k)))
    den = one
    for i in range(1, 5):
        den = mul(den, power(linear(a=1, b=1, c=i), 6))
    residual = add(mul(u, shifted), mul(v, x), -1)
    residual = add(residual, mul(univariate(data['q'][0]), den), -1)
    for ell, cs in enumerate(data['q'][1:]):
        term = mul(linear(a=-1, b=1), linear(a=2, b=1))
        for i in range(1, 2*ell+1):
            term = mul(term, linear(a=-1, b=1, c=-i))
        for i in range(1, 4*ell+1):
            term = mul(term, linear(a=2, b=1, c=i))
        for i in range(2*ell+1, 5):
            term = mul(term, power(linear(a=1, b=1, c=i), 6))
        residual = add(residual, mul(univariate(cs), term), -1)
    assert not residual, 'universal polynomial identity failed'
    assert all(c <= 0 for c in data['q'][0]) and any(c < 0 for c in data['q'][0])
    assert all(all(c >= 0 for c in cs) and any(c > 0 for c in cs) for cs in data['q'][1:])
    assert len(data['q'][0])-1 == 21

    recurrence = json.loads((root/'notes/pade-sign-recurrence-0.json').read_text())
    rows = []
    for n in (2, 4, 6, 8, 12, 20):
        q = [ev(cs, n) for cs in data['q']]
        factors = [prod((n+i)**3 for i in range(1, 2*ell+1)) for ell in range(3)]
        f = state(n)
        c = [-Q(q[ell+1], factors[ell]*q[0]) for ell in range(3)]
        target = coordinate(n, 1)
        assert target == [sum(c[i]*f[i][j] for i in range(3)) for j in range(3)]
        p = [ev(cs, n) for cs in recurrence['p']]
        a, b, cc = [-Q(value, p[3]) for value in p[:3]]
        transfer = [[Q(0), Q(1), Q(0)], [Q(0), Q(0), Q(1)], [a, b, cc]]
        next_state = state(n+2)
        assert matmul(transfer, f) == next_state
        w, next_w = determinant(f), determinant(next_state)
        assert w != 0 and next_w == -Q(p[0], p[3])*w
        ctransfer = compound(transfer)
        assert ctransfer == [[0, 0, 1], [-a, 0, cc], [0, -a, -b]]
        assert matmul(ctransfer, compound(f)) == compound(next_state)
        for j, (k, l) in enumerate(PAIRS):
            actual = f[0][k]*target[l]-f[0][l]*target[k]
            assert actual == c[1]*compound(f)[0][j]+c[2]*compound(f)[1][j]
        rows.append({'index': n, 'bridge_coefficients': list(map(str, c)),
                     'casoratian': str(w), 'casoratian_ratio': str(-Q(p[0], p[3])),
                     'period_coordinate_identity_verified': True,
                     'exterior_square_transport_verified': True})

    # Test the exact p-adic term formula; the all-index proof is in the note.
    local, hypergeometric_checks = [], 0
    for n in (2, 4, 8, 12):
        for m in (n, n-1):
            first = Q(factorial(n)**5 * factorial(m)**4 * factorial(n+2*m+1),
                      factorial(n+m+1)**6)
            for k in (0, 1, 2, 5):
                t = m+1+k
                direct = Q(factorial(n)**5, factorial(m)**2) * Q(
                    prod((t-j)*(t+n+j) for j in range(1, m+1)),
                    prod((t+j)**5 for j in range(n+1)))
                hypergeometric = first * Q(
                    prod(m+1+i for i in range(k))**6
                    * prod(n+2*m+2+i for i in range(k)),
                    prod(n+m+2+i for i in range(k))**6 * factorial(k))
                assert direct == hypergeometric
                hypergeometric_checks += 1
            for p in (2, 3, 5, 7):
                exponent = 1
                while p**exponent <= n+m:
                    exponent += 1
                for e in (exponent, exponent+1):
                    t = p**e
                    term = Q(factorial(n)**5, factorial(m)**2) * Q(
                        prod((t-j)*(t+n+j) for j in range(1, m+1)),
                        prod((t+j)**5 for j in range(n+1)))
                    actual = valuation(term.numerator, p)-valuation(term.denominator, p)
                    expected = valuation(comb(n+m, m), p)-5*e
                    assert actual == expected
                    local.append({'index': n, 'length': m, 'prime': p,
                                  'exponent': e, 'term_valuation': actual})
    return {'scope': 'Universal integer polynomial bridge certificate; paper boundary '
                     'argument identifies rational period coordinates. Finite checks of '
                     'coordinate transport and p-adic formulas. No winning gcd estimate.',
            'polynomial_identity_verified': True,
            'common_bridge_denominator_degree_at_most': 33,
            'hypergeometric_term_checks': hypergeometric_checks,
            'period_checks': rows, 'local_term_checks': local}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = verify(Path(__file__).resolve().parents[1])
    args.output.write_text(json.dumps(result, indent=2))
    print('Universal bridge identity: verified; period cases:', len(result['period_checks']),
          'local term checks:', len(result['local_term_checks']))


if __name__ == '__main__':
    main()
