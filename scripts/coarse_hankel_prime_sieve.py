"""Exact powered Hankel reconstruction and coarse local valuation checks."""
from fractions import Fraction as Q
from math import comb, factorial, gcd, lcm, log, prod
from pathlib import Path
import json
from check_hankel_moment_cutoff import bernoulli_numbers


def mul(a, b):
    c = [Q(0)]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i+j] += x*y
    return c


def D(k):
    result = [Q(1)]
    for j in range(1, k+1):
        result = mul(result, [j*j, 1])
    return result


def evaluate(poly, x):
    result = Q(0)
    for c in reversed(poly):
        result = result*x+c
    return result


def quotient_monic(a, b):
    a = a[:]
    if len(a) < len(b):
        return [Q(0)]
    out = [Q(0)]*(len(a)-len(b)+1)
    for i in range(len(out)-1, -1, -1):
        out[i] = a[i+len(b)-1]
        for j, c in enumerate(b):
            a[i+j] -= out[i]*c
    return out


def det(matrix):
    a = [row[:] for row in matrix]
    result = Q(1)
    for i in range(len(a)):
        pivot = next((j for j in range(i, len(a)) if a[j][i]), None)
        if pivot is None:
            return Q(0)
        if pivot != i:
            a[i], a[pivot] = a[pivot], a[i]
            result = -result
        value = a[i][i]
        result *= value
        for j in range(i+1, len(a)):
            scale = a[j][i]/value
            for k in range(i+1, len(a)):
                a[j][k] -= scale*a[i][k]
    return result


def interpolate(values):
    result = [Q(0)]*len(values)
    basis = [Q(1)]
    differences = values[:]
    for k in range(len(values)):
        for j, c in enumerate(basis):
            result[j] += differences[0]*c
        differences = [b-a for a, b in zip(differences, differences[1:])]
        basis = [c/(k+1) for c in mul(basis, [-k, 1])]
    return result


def vp(x, p):
    if not x:
        return None
    a, b, value = abs(x.numerator), x.denominator, 0
    while a % p == 0:
        a //= p
        value += 1
    while b % p == 0:
        b //= p
        value -= 1
    return value


def ilog(p, n):
    count = 0
    while n >= p:
        n //= p
        count += 1
    return count


def check(s, K, N):
    h = K-N
    DN, DK = D(N), D(K)
    numerator = [Q(1)]
    for _ in range(6):
        numerator = mul(numerator, DN)
    E = max(0, 6*N+2*h-2-K)
    B = bernoulli_numbers(2*E+2)
    mu = [(-1)**e*B[2*e+2]*Q(prod(range(2*e+3, 2*e+s+1)), factorial(s-1))
          for e in range(E+1)]
    harmonic = [Q(0)]
    for j in range(1, K+1):
        harmonic.append(harmonic[-1]+Q(1, j**s))
    residues = {j: evaluate(numerator, -j*j)/prod(k*k-j*j for k in range(1, K+1) if k != j)
                for j in range(N+1, K+1)}
    aa, bb = [], []
    for e in range(2*h-1):
        polynomial = quotient_monic([Q(0)]*e+numerator, DK)
        a = sum((c*mu[k] for k, c in enumerate(polynomial)), Q(0))
        b = Q(0)
        for j, residue in residues.items():
            c = residue*(-j*j)**e
            b += c*j**(s-1)
            a += c*(-j**(s-1)*harmonic[j]+Q(1, 2*j)-Q(1, s-1))
        aa.append(a)
        bb.append(b)
    values = [det([[aa[i+j]+x*bb[i+j] for j in range(h)] for i in range(h)])
              for x in range(h+1)]
    coefficients = interpolate(values)
    leading = (-1)**(h*(h-1)//2)*prod(j**(s-1)*evaluate(DN, -j*j)**5
                                     for j in range(N+1, K+1))
    assert coefficients[-1] == leading
    assert evaluate(coefficients, h+1) == det([
        [aa[i+j]+(h+1)*bb[i+j] for j in range(h)] for i in range(h)])
    scale = Q(factorial(K)**(2*h)*4**(h-1),
              factorial(N)**(12*h)*prod(factorial(2*i)**2 for i in range(1, h)))
    normalized = [scale*c for c in coefficients]
    d = s+12*N+4*h-4
    cutoff = d+1
    primes = [p for p in range(2, cutoff+2)
              if all(p % j for j in range(2, int(p**0.5)+1))]
    checks = []
    for p in primes:
        actual = min(vp(c, p) for c in normalized if c)
        bound = -(s+1)*h*ilog(p, cutoff)-h*vp(Q(factorial(s-1)), p)
        assert actual >= bound, (s, K, N, p, actual, bound)
        checks.append({'p': p, 'gauss_valuation': actual, 'lower_bound': bound})
    denominator = lcm(*(Q(c, leading).denominator for c in coefficients))
    return {'weight': s, 'K': K, 'N': N, 'degree': h,
            'monic_denominator': str(denominator), 'prime_checks': checks}


def main():
    records = [check(s, K, N) for K, N in [(6, 1), (8, 1), (10, 1), (12, 1)]
               for s in [5, 7, 9]]
    comparisons = []
    for i in range(0, len(records), 3):
        base = records[i]
        comparisons.append({'K': base['K'], 'N': base['N'],
            'log_d7_over_d5_per_K_squared':
                (log(int(records[i+1]['monic_denominator']))-
                 log(int(base['monic_denominator'])))/base['K']**2})
    target = Path(__file__).resolve().parents[1]/'notes/coarse-hankel-prime-sieve.json'
    target.write_text(json.dumps({'records': records, 'finite_relative_costs': comparisons,
        'small_prime_bound_proved_on_paper': True,
        'full_irrationality_bound_proved': False}, indent=2))
    print(len(records), 'exact Hankel polynomials;', sum(len(r['prime_checks']) for r in records),
          'local valuation checks passed', flush=True)
    print(comparisons, flush=True)


if __name__ == '__main__':
    main()
