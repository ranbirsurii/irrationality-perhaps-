"""Exact checks supporting the paper lower-column prime-divisibility proof."""

import argparse
from fractions import Fraction as Q
from functools import lru_cache
import json
from math import comb, gcd, lcm, prod
from pathlib import Path
import sys

from audit_prime_density_candidate import quantities
from audit_primitive_normalization import weight_five_coordinates
from audit_smith_lattice import primes_to
from pade_coefficient_sign import alpha


def mod_rational(value, p):
    value = Q(value)
    assert divmod(value.denominator, p)[1] != 0
    return divmod(value.numerator*pow(value.denominator, -1, p), p)[1]


@lru_cache(None)
def raw_top(r, s):
    return sum((-1)**(s+j)*comb(r,j)**5*comb(j+s,s)*comb(r-j+s,s)
               for j in range(r+1))


def verify(root):
    data = json.loads((root/'notes/three-block-lattice-audit.json').read_text())['cases']
    congruences, divisor_checks = [], []
    for row in data:
        n = row['index']
        if n < 6:
            continue
        d = lcm(*range(1,n+1))
        coordinates = [[Q(int(x),d**5) for x in r] for r in row['cleared_coordinate_rows']]
        values = [r[0] for r in coordinates]
        boundary = prod(n-j for j in range(3))*prod(3*n-j for j in range(13))
        certified = d**3
        for p in primes_to(3*n//2):
            if p > n:
                assert all(mod_rational(a,p)==0 for a in values)
                certified *= p
                continue
            if p <= 5 or p*p <= 3*n+6:
                continue
            q,r = divmod(n,p)
            if r >= 2:
                aq = alpha(q,q)
                for i,vector in enumerate(coordinates):
                    factor=raw_top(r,r-i)
                    if q & 1:
                        assert factor==0 and aq==0
                        expected=[0,0,0]
                    else:
                        expected=[factor*x for x in weight_five_coordinates(q,q)]
                    scaled=[p*p*vector[0],vector[1],p**5*vector[2]]
                    left=[mod_rational(x,p) for x in scaled]
                    right=[mod_rational(x,p) for x in expected]
                    assert left == right,(n,p,i,left,right)
                    congruences.append({'index':n,'prime':p,'offset':i,
                                        'quotient':q,'residue':r,'modular_values':left})
            if divmod(boundary,p)[1] == 0:
                continue
            carry = (3*n)//(2*p)-3*(n//(2*p))
            if carry > 0:
                assert all(mod_rational(p*p*a,p)==0 for a in values)
                certified *= p
        g = gcd(*(int(r[0]) for r in row['cleared_coordinate_rows']))
        assert divmod(g,certified)[1] == 0
        divisor_checks.append({'index':n,'certified_lower_column_divisor':str(certified),
                               'actual_lower_column_gcd':str(g)})

    all_block_count = 0
    for n in (6,8,10,12,16,20,30,40):
        for p in primes_to(3*n//2):
            if p <= n or p <= 5:
                continue
            for m in range(n+1):
                assert mod_rational(weight_five_coordinates(n,m)[0],p)==0
                all_block_count += 1
    return {'scope':'Finite exact checks of a congruence and explicit divisors whose '
                    'general proofs are in lower-column-prime-divisibility.md. '
                    'No image-content or final primitive-cost estimate is asserted.',
            'frobenius_congruence_checks':congruences,
            'certified_divisor_checks':divisor_checks,
            'all_block_interval_prime_checks':all_block_count}


def main():
    sys.set_int_max_str_digits(200000)
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',required=True,type=Path)
    args=parser.parse_args()
    result=verify(Path(__file__).resolve().parents[1])
    args.output.write_text(json.dumps(result,indent=2))
    print('Congruence cases:',len(result['frobenius_congruence_checks']),
          'explicit divisor cases:',len(result['certified_divisor_checks']),
          'all-block cases:',result['all_block_interval_prime_checks'])


if __name__=='__main__':
    main()
