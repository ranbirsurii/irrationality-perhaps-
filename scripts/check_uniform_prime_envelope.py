"""Exact checks of the proved all-index envelope; no extrapolation."""

from fractions import Fraction as Q
from itertools import combinations
from math import comb, factorial, lcm, prod
from pathlib import Path
import json

from audit_smith_lattice import primes_to
from check_integral_cancellation import normalized_log_jet_coordinates
from integer_determinants import bareiss
from symmetric_pade_audit import poised_period_coordinates


def rational_mod(x, p):
    x = Q(x)
    assert x.denominator % p
    return x.numerator * pow(x.denominator, -1, p) % p


def mul(a, b, p):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] = (out[i + j] + x * y) % p
    return trim(out)


def trim(a):
    while len(a) > 1 and not a[-1]:
        a.pop()
    return a


def power(a, e, p):
    out = [1]
    for _ in range(e):
        out = mul(out, a, p)
    return out


def add(a, b, scale, p):
    out = a + [0] * max(0, len(b) - len(a))
    for i, x in enumerate(b):
        out[i] = (out[i] + scale * x) % p
    return trim(out)


def check_trace(s, n, m, p, coordinates):
    assert p > n >= s - 1
    numerator = [1]
    for v in range(1, m + 1):
        numerator = mul(numerator, [-v % p, 1], p)
        numerator = mul(numerator, [(n + v) % p, 1], p)
    missing = set(range(p)) - {-h % p for h in range(n + 1)}
    P = numerator
    for a in sorted(missing):
        P = mul(P, power([-a % p, 1], s, p), p)
    scale = factorial(n) ** s * pow(factorial(m) ** 2, -1, p) % p
    P = [(scale * x) % p for x in P]
    trace = [0] * len(P)
    for degree, value in enumerate(P):
        for exponent in range(p - 1, degree + 1, p - 1):
            trace[degree - exponent] = (
                trace[degree - exponent] - value * comb(degree, exponent)) % p
    trace = trim(trace)
    F = [0, p - 1] + [0] * (p - 2) + [1]
    expected = [0]
    for q in range(3, s + 1, 2):
        value = rational_mod(coordinates[(q - 3) // 2], p)
        expected = add(expected, power(F, s - q, p), -value, p)
    assert trace == expected, (s, n, m, p)
    bound = (s - 1) * p + 2 * m - s * n - s + 1
    assert trace == [0] or len(trace) - 1 <= bound


def check_case(s, n):
    r = (s - 1) // 2
    d = lcm(*range(1, n + 1))
    polynomial = (n + 1) * ((s + 2) * n + s) ** (s - 1)
    old_E = polynomial * 2 ** ((s + 3) * n)
    E = polynomial * comb(n, n // 2) ** s * comb(3 * n // 2, n) ** 2
    assert E <= old_E
    primes = primes_to((s - 2) * n // 2)
    divisors = {k: prod(p for p in primes if n < p <= (s - 2) * n // (k - 1))
                for k in range(3, s - 1, 2)}
    blocks = {}
    prime_checks = 0
    trace_checks = 0
    for m in range(n + 1):
        first = normalized_log_jet_coordinates(s, n, m)
        scale = Q(factorial(n) ** s, factorial(m) ** 2)
        second = [scale * x for x in poised_period_coordinates(r, n, m)]
        assert first == second
        assert all(abs(x) <= E for x in first[:-1])
        for k, G in divisors.items():
            coefficient = first[(k - 3) // 2] * d ** (s - k)
            assert coefficient.denominator == 1
            assert int(coefficient) % G == 0
            prime_checks += sum(1 for p in primes if n < p <= (s - 2) * n // (k - 1))
        if m in (0, n):
            for p in primes:
                if n < p <= (s - 2) * n // 2:
                    check_trace(s, n, m, p, first)
                    trace_checks += 1
        blocks[m] = first
    rows = [[int(blocks[n - j][q - 1] * d ** (s - (2 * q + 1)))
             // divisors[2 * q + 1] for j in range(r + 1)]
            for q in range(1, r)]
    I = next(cols for cols in combinations(range(r + 1), r - 1)
             if bareiss([[row[j] for j in cols] for row in rows]))
    A = [[row[j] for j in I] for row in rows]
    delta = bareiss(A)
    H = [Q(d ** (s - (2 * q + 1)) * E, divisors[2 * q + 1])
         for q in range(1, r)]
    assert all(abs(value) <= H[i] for i, row in enumerate(rows) for value in row)
    limit = factorial(r) * prod(H)
    vectors = []
    for free in set(range(r + 1)) - set(I):
        w = [0] * (r + 1)
        w[free] = delta
        for j, pivot in enumerate(I):
            replaced = [row[:] for row in A]
            for i in range(r - 1):
                replaced[i][j] = rows[i][free]
            w[pivot] = -bareiss(replaced)
        assert all(sum(x * y for x, y in zip(row, w)) == 0 for row in rows)
        assert sum(map(abs, w)) <= limit
        vectors.append(w)
    assert len(vectors) == 2
    return {'weight': s, 'index': n, 'all_block_count': n + 1,
            'independent_coefficient_algorithms_agree': True,
            'sharper_central_binomial_envelope_verified': True,
            'coefficient_envelope_checks': (n + 1) * r,
            'prime_divisibility_checks': prime_checks,
            'full_translation_trace_polynomial_checks': trace_checks,
            'lower_row_prime_products': {str(k): str(v) for k, v in divisors.items()},
            'cramer_cancellation_vectors': vectors,
            'divisor_refined_mass_envelope_verified': True}


def main():
    cases = [check_case(s, n) for s, n in ((5, 4), (7, 6), (7, 8), (7, 10),
                                          (9, 8), (9, 10), (11, 10))]
    result = {'scope': 'Finite independent checks supporting the all-index paper proof; '
                       'not an asymptotic proof or an irrationality conclusion.',
              'cases': cases,
              'required_primitive_cost_rate_proved': False}
    destination = Path(__file__).resolve().parents[1] / 'notes/uniform-prime-envelope-checks.json'
    destination.write_text(json.dumps(result, indent=2), encoding='utf-8')
    print(json.dumps({'cases': len(cases),
                      'coefficient_envelope_checks': sum(x['coefficient_envelope_checks'] for x in cases),
                      'prime_divisibility_checks': sum(x['prime_divisibility_checks'] for x in cases),
                      'full_trace_checks': sum(x['full_translation_trace_polynomial_checks'] for x in cases)},
                     indent=2))


if __name__ == '__main__':
    main()
