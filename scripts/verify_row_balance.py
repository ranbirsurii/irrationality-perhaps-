"""Verify universal recurrence identities used in the row-balance proof."""

import json
from fractions import Fraction as Q
from pathlib import Path

from verify_sign_recurrences import add, linear, mul, power, univariate


def verify_certificate(data):
    offset = data['offset']
    one, t, t1 = linear(c=1), linear(b=1), linear(b=1, c=1)
    x, xshift = {}, {}
    for k, cs in enumerate(data['x']):
        x = add(x, mul(univariate(cs), power(t, k)))
        xshift = add(xshift, mul(univariate(cs), power(t1, k)))
    u = mul(power(t, 6), linear(a=2, b=1, c=1-offset))
    v = mul(linear(a=-1, b=1, c=offset-1),
            power(linear(a=1, b=1, c=6), 6))
    residual = add(mul(u, xshift), mul(v, x), -1)
    for ell, cs in enumerate(data['q']):
        term = one
        for i in range(1, 2*ell+1):
            term = mul(term, linear(a=-1, b=1, c=offset-i))
        for i in range(1, 4*ell+1):
            term = mul(term, linear(a=2, b=1, c=i-offset))
        for i in range(2*ell+1, 7):
            term = mul(term, power(linear(a=1, b=1, c=i), 6))
        residual = add(residual, mul(univariate(cs), term), -1)
    assert not residual
    if offset == 2:
        common = univariate(data['common_factor_coefficients'])
        expected = linear(a=1, c=1)
        for i in range(2, 7):
            expected = mul(expected, power(linear(a=1, c=i), 3))
        assert common == expected
    else:
        common = one
        for i in data['common_factor_shifts']:
            common = mul(common, power(linear(a=1, c=i), 3))
    for ell in range(4):
        factor = one
        for i in range(2*ell+1, 7):
            factor = mul(factor, power(linear(a=1, c=i), 3))
        assert mul(univariate(data['q'][ell]), factor) == \
            mul(common, univariate(data['p'][ell]))
    degrees = [len(cs)-1 for cs in data['p']]
    assert len(set(degrees)) == 1
    limiting = [-Q(cs[-1], data['p'][3][-1]) for cs in data['p'][:3]]
    assert limiting == [729, -15146217, -30510]
    return degrees[0]


def verify():
    root = Path(__file__).resolve().parents[1]
    files = ['pade-sign-recurrence-0.json', 'pade-sign-recurrence-1.json',
             'pade-offset-two-recurrence.json']
    degrees = [verify_certificate(json.loads((root/'notes'/name).read_text()))
               for name in files]
    assert degrees == [25, 36, 46]
    def characteristic(z):
        return z**3-30510*z*z+15146217*z+729
    assert characteristic(-1) < 0 < characteristic(0)
    assert characteristic(1) > 0 > characteristic(1000)
    assert characteristic(30005) < 0 < characteristic(30006)
    print('Three universal polynomial certificates and normalization identities verified.')
    print('Common limiting coefficients: 729, -15146217, -30510.')
    print('Signed characteristic roots lie in (-1,0), (1,1000), (30005,30006).')
    print('No family indices or finite recurrence samples were evaluated.')


if __name__ == '__main__':
    verify()
