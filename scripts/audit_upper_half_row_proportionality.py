"""Reconstruct upper-half prime row congruences from exact Laurent jets."""
from fractions import Fraction as Q
from math import gcd, lcm
from pathlib import Path
import argparse
import json
from check_integral_cancellation import normalized_log_jet_coordinates, harmonic, maximal_content


def primes_through(n):
    return [p for p in range(11, n+1)
            if all(p % d for d in range(2, int(p**0.5)+1))]


def residue(x, modulus):
    assert gcd(x.denominator, modulus) == 1
    return x.numerator*pow(x.denominator, -1, modulus) % modulus


def check_rows(rows, n, p, scalar_by_prime):
    modulus = p*p
    u = [residue(p**3*row[0], modulus) for row in rows]
    z = [residue(p**6*row[3], modulus) for row in rows]
    pivot = next((i for i in range(4) if u[i] % p), None)
    if p not in scalar_by_prime:
        if pivot is None:
            return {'n': n, 'p': p, 'status': 'no_unit_pivot_yet', 'u': u, 'z': z}
        scalar_by_prime[p] = z[pivot]*pow(u[pivot], -1, modulus) % modulus
    scalar = scalar_by_prime[p]
    defects = [(zi-scalar*ui) % modulus for ui, zi in zip(u, z)]
    return {'n': n, 'p': p, 'scalar_mod_p_squared': scalar,
            'status': 'passed' if not any(defects) else 'failed',
            'defects': defects, 'has_unit_pivot': pivot is not None}


def fifth_order_defects(rows, p):
    H2 = harmonic(p-1, 2)
    return [residue(174*p**7*row[3] + (191+87*p*p*H2)*p**4*row[0]
                    +247*p*p*row[1], p**5) for row in rows]


def content_control(n, p):
    D = lcm(*range(1, n+1))**7
    cols = [normalized_log_jet_coordinates(7, n, n-j) for j in range(4)]
    cleared = [[D*column[k] for column in cols] for k in range(4)]
    assert all(x.denominator == 1 for row in cleared for x in row)
    rows = [[int(x) for x in row] for row in cleared]
    lower = maximal_content(rows[:2])
    joint = gcd(maximal_content(rows[:2]+[rows[2]]),
                maximal_content(rows[:2]+[rows[3]]))
    assert joint % lower == 0
    gamma = joint//lower
    v = 0
    while gamma % p == 0:
        gamma //= p
        v += 1
    assert v >= (4 if p == 29 else 5)
    return {'n': n, 'p': p, 'exact_image_content_valuation': v}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--max-index', type=int, default=240)
    args = parser.parse_args()
    primes = primes_through(args.max_index)
    scalar_by_prime = {}
    records = []
    for n in range(6, args.max_index+1, 2):
        rows = [normalized_log_jet_coordinates(7, n, n-j) for j in range(4)]
        for p in primes:
            if n//2 < p <= n-3:
                record = check_rows(rows, n, p, scalar_by_prime)
                assert record['scalar_mod_p_squared'] == -153*pow(98, -1, p*p) % (p*p)
                record['fifth_order_defects'] = fifth_order_defects(rows, p)
                assert not any(record['fifth_order_defects'])
                records.append(record)
        if n % 40 == 0:
            print('checked through', n, 'pairs', len(records), flush=True)
    boundary = []
    for n, p in [(60, 59), (80, 79)]:
        rows = [normalized_log_jet_coordinates(7, n, n-j) for j in range(4)]
        boundary.append(check_rows(rows, n, p, scalar_by_prime))
    report = {'maximum_index': args.max_index,
              'normalization': 'u=p^3*a3, z=p^6*b; common (d_n/p)^7 unit cancels',
              'records': records, 'boundary_controls': boundary,
              'failures': [row for row in records if row['status'] == 'failed'],
              'no_unit_pivot': [row for row in records if row['status'] == 'no_unit_pivot_yet'],
              'content_controls': [content_control(n, p) for n, p in
                  [(32, 29), (60, 41), (80, 53), (100, 79), (102, 67), (120, 83)]],
              'scope': 'Finite exact tests; the uniform proof is in upper-half-row-congruence.tex'}
    target = Path(__file__).resolve().parents[1]/'notes/upper-half-row-proportionality.json'
    target.write_text(json.dumps(report, indent=2))
    print('pairs', len(records), 'failures', len(report['failures']),
          'unresolved pivot cases', len(report['no_unit_pivot']))
    assert not report['failures']
    assert not report['no_unit_pivot']


if __name__ == '__main__':
    main()
