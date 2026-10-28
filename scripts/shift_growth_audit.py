from fractions import Fraction as Q
from functools import lru_cache
from math import gcd, log, prod
from pathlib import Path
import argparse
import json
import sys
from integer_determinants import bareiss


@lru_cache(None)
def primes_to(a):
    flags = bytearray(b'\x01') * (a + 1)
    flags[:2] = b'\x00\x00'
    for p in range(2, int(a ** 0.5) + 1):
        if flags[p]:
            flags[p * p:a + 1:p] = b'\x00' * ((a - p * p) // p + 1)
    return tuple(p for p in range(2, a + 1) if flags[p])


@lru_cache(None)
def third_prime_product(s, a):
    primes = tuple(p for p in primes_to(a) if a < 3 * p and (2 ** s + 1) % p)
    return prod(primes), len(primes)


def exact_binary_floor_ratio(numerator, denominator):
    assert numerator > 0 and denominator > 0
    b = numerator.bit_length() - denominator.bit_length()
    if (numerator < denominator << b) if b >= 0 else (numerator << -b < denominator):
        b -= 1
    assert (numerator >= denominator << b) if b >= 0 else (numerator << -b >= denominator)
    return b


def centered_certificate(s, size, shift):
    delta = [Q(0)]
    for k in range(1, 2 * size - 1):
        delta.append(delta[-1] + Q(1, (shift + k) ** s))
    scale = prod((shift + k) ** s for k in range(1, 2 * size - 1))
    base = [[-scale * delta[i + j] for j in range(size)] for i in range(size)]
    assert all(x.denominator == 1 for row in base for x in row)
    base = [[int(x) for x in row] for row in base]
    c = bareiss(base)
    m = bareiss([[x + scale for x in row] for row in base]) - c
    cost = scale ** size
    assert 0 < m <= cost
    harmonic = sum((Q(1, k ** s) for k in range(1, shift + 1)), Q(0))
    approximation = harmonic - Q(c, m)
    p, u = approximation.numerator, approximation.denominator
    assert harmonic == Q(p, u) + Q(c, m)
    prime_product, prime_count = third_prime_product(s, shift)
    prime_power = prime_product ** s
    assert harmonic.denominator % prime_power == 0
    assert (u * m) % prime_power == 0
    assert prime_power <= u * cost
    target = size ** (s - 1) * (size + shift) ** (s - 1)
    return {'weight': s, 'size': size, 'shift': shift,
            'centered_scale': str(scale), 'centered_coefficient_m': str(m),
            'centered_constant_c': str(c),
            'primitive_approximation_numerator': str(p),
            'primitive_target_coefficient': str(u),
            'prime_count': prime_count,
            'prime_product_power_divides_harmonic_denominator': True,
            'prime_product_power_divides_u_times_m': True,
            'actual_height_excess_bits': exact_binary_floor_ratio(u, target)}


def main():
    sys.set_int_max_str_digits(200000)
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    exact_rows, lower_rows = [], []
    for s in (3, 5, 7, 9):
        for size, shift in ((3, 27), (5, 125), (8, 512), (8, 4096)):
            row = centered_certificate(s, size, shift)
            exact_rows.append(row)
            print('centered', s, size, shift, 'actual excess bits',
                  row['actual_height_excess_bits'], flush=True)
        for size, power in ((30, 3), (40, 3), (60, 3), (100, 3), (8, 4), (12, 4), (20, 4)):
            shift = size ** power
            prime_product, count = third_prime_product(s, shift)
            prime_power = prime_product ** s
            cost = prod((shift + k) ** s for k in range(1, 2 * size - 1)) ** size
            target = size ** (s - 1) * (size + shift) ** (s - 1)
            bits = exact_binary_floor_ratio(prime_power, cost * target)
            row = {'weight': s, 'size': size, 'shift': shift, 'shift_power': power,
                   'prime_count': count, 'prime_power_bit_length': prime_power.bit_length(),
                   'centered_cost_bit_length': cost.bit_length(),
                   'certified_height_excess_bits': bits,
                   'scope': 'Exact finite consequence of the proved prime-denominator and '
                            'centered-coefficient inequalities.'}
            lower_rows.append(row)
            print('lower bound', s, size, shift, 'excess bits', bits, flush=True)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps({
        'scope': 'Exact centered harmonic and large-shift lower certificates; '
                 'no all-odd irrationality claim.',
        'centered_rows': exact_rows, 'lower_bound_rows': lower_rows}, indent=2), encoding='utf-8')


if __name__ == '__main__':
    main()
