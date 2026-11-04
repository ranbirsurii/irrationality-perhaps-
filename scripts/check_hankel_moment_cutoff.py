"""Check the exact prime support of the polynomial Hankel moments."""
from fractions import Fraction as Q
from math import comb, factorial, prod
from pathlib import Path
import json


def bernoulli_numbers(n):
    values = [Q(1)]
    for m in range(1, n+1):
        values.append(-sum((comb(m+1, j)*values[j] for j in range(m)), Q(0))/(m+1))
    return values


def main():
    K = 80
    N = 6
    E = K+4*N-2
    B = bernoulli_numbers(2*E+2)
    primes = [p for p in range(2, 2*E+4)
              if all(p % d for d in range(2, int(p**0.5)+1))]
    tests = 0
    profiles = []
    weight_five_moments = [(-1)**e*B[2*e+2]*Q(prod(range(2*e+3, 2*e+6)), 24)
                           for e in range(E+1)]
    for s in [5, 7, 9, 11, 13]:
        bad_primes = set()
        comparison_constant = factorial(s-1)//24
        for e in range(E+1):
            L = 2*e+2
            moment = (-1)**e*B[L]*Q(prod(range(L+1, L+s-1)), factorial(s-1))
            integer_multiplier = prod(range(L+4, L+s-1))
            assert comparison_constant*moment == integer_multiplier*weight_five_moments[e]
            assert (comparison_constant*weight_five_moments[e].denominator) % moment.denominator == 0
            for p in primes:
                if p <= s:
                    continue
                predicted_bad = L % (p-1) == 0 and (L//(p-1)) % p not in range(1, s-1)
                actual_bad = moment.denominator % p == 0
                assert actual_bad == predicted_bad
                if actual_bad:
                    bad_primes.add(p)
                    assert (s-1)*(p-1) <= L <= 2*E+2
                tests += 1
        profiles.append({'weight': s, 'maximum_degree': E,
                         'possible_denominator_prime_cutoff': str(1+Q(2*E+2, s-1)),
                         'observed_denominator_primes_above_weight': sorted(bad_primes)})
    target = Path(__file__).resolve().parents[1]/'notes/hankel-moment-cutoff.json'
    target.write_text(json.dumps({'profiles': profiles, 'exact_prime_tests': tests,
        'exact_weight_raise_identities_checked': len(profiles)*(E+1),
        'full_hankel_denominator_transfer_proved': False}, indent=2))
    print(tests, 'exact moment denominator support tests passed')
    for profile in profiles:
        print(profile)


if __name__ == '__main__':
    main()
