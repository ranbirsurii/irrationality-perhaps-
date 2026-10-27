from fractions import Fraction as Q
from functools import lru_cache
from math import factorial, prod


@lru_cache(None)
def even_bernoulli_numbers(order):
    row, result = [], []
    for m in range(2 * order + 1):
        row.append(Q(1, m + 1))
        for j in range(m, 0, -1):
            row[j - 1] = j * (row[j - 1] - row[j])
        if m >= 2 and m % 2 == 0:
            result.append(row[0])
    assert result[0] == Q(1, 6)
    return tuple(result)


@lru_cache(None)
def euler_maclaurin_zeta_interval(s, order=96):
    assert s >= 2 and order >= 1
    m = 10 * order
    partial = sum((Q(1, k ** s) for k in range(1, m)), Q(0))
    value = partial + Q(1, (s - 1) * m ** (s - 1)) + Q(1, 2 * m ** s)
    for k, b in enumerate(even_bernoulli_numbers(order), 1):
        term = b * Q(prod(range(s, s + 2 * k - 1)), factorial(2 * k)) / m ** (s + 2 * k - 1)
        value += term
    radius = abs(term)
    assert radius > 0
    lo, hi = value - radius, value + radius
    integral_lo = partial + Q(1, (s - 1) * m ** (s - 1))
    integral_hi = integral_lo + Q(1, m ** s)
    assert integral_lo <= lo <= hi <= integral_hi
    return lo, hi
