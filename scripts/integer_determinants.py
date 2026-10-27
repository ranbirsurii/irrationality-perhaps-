from fractions import Fraction as Q
from math import lcm, prod


def bareiss(matrix):
    n = len(matrix)
    if n == 0:
        return 1
    a = [row[:] for row in matrix]
    previous, sign = 1, 1
    for k in range(n - 1):
        pivot_row = next((i for i in range(k, n) if a[i][k]), None)
        if pivot_row is None:
            return 0
        if pivot_row != k:
            a[k], a[pivot_row] = a[pivot_row], a[k]
            sign = -sign
        pivot = a[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                numerator = pivot * a[i][j] - a[i][k] * a[k][j]
                value, remainder = divmod(numerator, previous)
                assert remainder == 0
                a[i][j] = value
            a[i][k] = 0
        previous = pivot
    return sign * a[-1][-1]


def clear_rows(matrix):
    scales = [lcm(*(v.denominator for v in row)) for row in matrix]
    integer = [[int(v * scale) for v in row] for row, scale in zip(matrix, scales)]
    assert all(Q(integer[i][j], scales[i]) == matrix[i][j]
               for i in range(len(matrix)) for j in range(len(matrix)))
    return scales, integer


def rational_determinant(matrix):
    scales, integer = clear_rows(matrix)
    return Q(bareiss(integer), prod(scales))


def interpolate_integer_values(values):
    differences = [Q(v) for v in values]
    coefficients = [Q(0) for _ in values]
    basis = [Q(1)]
    for k in range(len(values)):
        for i, v in enumerate(basis):
            coefficients[i] += differences[0] * v
        differences = [differences[i + 1] - differences[i]
                       for i in range(len(differences) - 1)]
        updated = [Q(0)] * (len(basis) + 1)
        for i, v in enumerate(basis):
            updated[i] -= v * k / (k + 1)
            updated[i + 1] += v / (k + 1)
        basis = updated
    assert all(c.denominator == 1 for c in coefficients)
    return [int(c) for c in coefficients]


def polynomial_value(coefficients, x):
    total = 0
    for c in reversed(coefficients):
        total = total * x + c
    return total


def adjugate_column(matrix, column):
    n = len(matrix)
    a = [row[:] + [int(i == column)] for i, row in enumerate(matrix)]
    previous, sign = 1, 1
    for k in range(n - 1):
        pivot_row = next((i for i in range(k, n) if a[i][k]), None)
        assert pivot_row is not None
        if pivot_row != k:
            a[k], a[pivot_row] = a[pivot_row], a[k]
            sign = -sign
        pivot = a[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n + 1):
                value, remainder = divmod(pivot * a[i][j] - a[i][k] * a[k][j], previous)
                assert remainder == 0
                a[i][j] = value
            a[i][k] = 0
        previous = pivot
    determinant = sign * a[-1][-2]
    assert determinant != 0
    solution = [Q(0)] * n
    for i in range(n - 1, -1, -1):
        solution[i] = (Q(a[i][-1]) - sum((a[i][j] * solution[j]
                                       for j in range(i + 1, n)), Q(0))) / a[i][i]
    answer = [determinant * x for x in solution]
    assert all(x.denominator == 1 for x in answer)
    answer = [int(x) for x in answer]
    assert all(sum(matrix[i][j] * answer[j] for j in range(n)) == determinant * int(i == column)
               for i in range(n))
    return determinant, answer


def interval_polynomial(coefficients, interval):
    lo = hi = Q(0)
    xlo, xhi = interval
    for c in reversed(coefficients):
        possibilities = (lo * xlo, lo * xhi, hi * xlo, hi * xhi)
        lo, hi = min(possibilities) + c, max(possibilities) + c
    return lo, hi
