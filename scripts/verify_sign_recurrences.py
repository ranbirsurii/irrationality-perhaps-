from fractions import Fraction as Q
from math import comb
from pathlib import Path
import argparse
import json
from pade_coefficient_sign import alpha


def add(a, b, scale=1):
    c = a.copy()
    for key, value in b.items():
        c[key] = c.get(key, 0) + scale * value
        if not c[key]:
            del c[key]
    return c


def mul(a, b):
    c = {}
    for (i, j), x in a.items():
        for (k, l), y in b.items():
            key = i + k, j + l
            c[key] = c.get(key, 0) + x * y
    return {key: value for key, value in c.items() if value}


def power(a, n):
    result = {(0, 0): 1}
    for _ in range(n):
        result = mul(result, a)
    return result


def univariate(cs):
    return {(i, 0): c for i, c in enumerate(cs) if c}


def linear(a=0, b=0, c=0):
    return {(i, j): v for (i, j), v in (((1, 0), a), ((0, 1), b), ((0, 0), c)) if v}


def ev(cs, n):
    result = 0
    for c in reversed(cs):
        result = c + n * result
    return result


def verify(path):
    data = json.loads(path.read_text())
    offset = data['offset']
    one, t, t1 = linear(c=1), linear(b=1), linear(b=1, c=1)
    x = {}
    xshift = {}
    for k, cs in enumerate(data['x']):
        x = add(x, mul(univariate(cs), power(t, k)))
        xshift = add(xshift, mul(univariate(cs), power(t1, k)))
    a = mul(power(t, 6), linear(a=2, b=1, c=1-offset))
    b = mul(linear(a=-1, b=1, c=offset-1), power(linear(a=1, b=1, c=6), 6))
    residual = add(mul(a, xshift), mul(b, x), -1)
    for ell, cs in enumerate(data['q']):
        term = one
        for i in range(1, 2 * ell + 1):
            term = mul(term, linear(a=-1, b=1, c=offset-i))
        for i in range(1, 4 * ell + 1):
            term = mul(term, linear(a=2, b=1, c=i-offset))
        for i in range(2 * ell + 1, 7):
            term = mul(term, power(linear(a=1, b=1, c=i), 6))
        residual = add(residual, mul(univariate(cs), term), -1)
    assert not residual, ('nonzero telescoping polynomial', offset)
    common = one
    for i in data['common_factor_shifts']:
        common = mul(common, power(linear(a=1, c=i), 3))
    for ell in range(4):
        factorial_factor = one
        for i in range(2 * ell + 1, 7):
            factorial_factor = mul(factorial_factor, power(linear(a=1, c=i), 3))
        assert mul(univariate(data['q'][ell]), factorial_factor) == \
            mul(common, univariate(data['p'][ell]))
    p = [univariate(cs) for cs in data['p']]
    omega = add(add(add({}, p[2], 10**6), p[3], -10**9), p[1], -1000)
    omega = add(omega, p[0])
    candidates = [add({}, p[0], -1), p[1], p[2], p[3], omega]
    for candidate, cs in zip(candidates, data['positive_shifted']):
        shifted = {}
        for (degree, zero), c in candidate.items():
            assert zero == 0
            shifted = add(shifted, power(linear(a=1, c=2), degree), c)
        assert shifted == univariate(cs)
        assert cs[0] > 0 and all(c >= 0 for c in cs)
    initial = []
    for n in (2, 4, 6):
        value = alpha(n, n-offset) / (n*n if offset else 1)
        initial.append((-1)**(n//2+offset)*value)
    assert initial[0] > 0
    assert initial[1] >= 1000*initial[0]
    assert initial[2] >= 1000*initial[1]
    for n in range(2, 22, 2):
        terms = [alpha(n+2*ell, n+2*ell-offset) /
                 ((n+2*ell)**2 if offset else 1) for ell in range(4)]
        assert sum(ev(cs, n)*value for cs, value in zip(data['p'], terms)) == 0
    return {'offset': offset, 'polynomial_identity': True,
            'universal_cone_inequalities': True, 'start_index': 2, 'ratio_bound': 1000,
            'initial_values': list(map(str, initial)),
            'recurrence_degrees': [len(cs)-1 for cs in data['p']]}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--certificates', type=Path,
                        default=Path(__file__).resolve().parent.parent/'notes')
    args = parser.parse_args()
    result = [verify(args.certificates/f'pade-sign-recurrence-{i}.json') for i in (0, 1)]
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
