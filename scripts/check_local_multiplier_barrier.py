"""Exact checks for the signed multiplier maximum on a shrinking disk."""
from fractions import Fraction as Q
from math import comb
import json
from pathlib import Path


def check(n, m):
    c = [(-1)**j * comb(n+2*m+1, m-j) * comb(n+j, j)
         for j in range(m+1)]
    moments = [comb(n+k, k)*comb(2*m-k, m-k) for k in range(m+1)]
    for k, moment in enumerate(moments):
        assert sum(c[j]*comb(j, k) for j in range(k, m+1)) == (-1)**k*moment
        assert 2**k*comb(2*m-k, m-k) <= comb(2*m, m)
    rho = Q(1, n+1)
    center_value = sum((Q(cj)*(1-rho)**j for j, cj in enumerate(c)), Q(0))
    disk_max = sum((moment*rho**k for k, moment in enumerate(moments)), Q(0))
    assert center_value == disk_max
    assert 0 < disk_max <= 2*comb(2*m, m)
    assert comb(2*m, m)**2*(3*m+1) <= 16**m
    if m <= n:
        normalized = disk_max/Q(4**n)
        assert normalized**2*(3*m+1) <= Q(4, 16**(n-m))


def main():
    count = 0
    for n in range(41):
        for m in range(n+1):
            check(n, m)
            count += 1
    report = {'profiles_checked': count, 'maximum_index': 40,
              'local_polynomial_bound': 'proved on paper; exact finite checks passed',
              'full_integer_form_cost_transfer_proved': False}
    target = Path(__file__).resolve().parents[1]/'notes/local-multiplier-barrier.json'
    target.write_text(json.dumps(report, indent=2))
    print(count, 'exact polynomial, moment, disk-majorant and central-binomial checks passed')


if __name__ == '__main__':
    main()
