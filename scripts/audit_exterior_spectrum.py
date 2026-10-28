"""Exact spectrum calculation and a counterexample to spectral Smith growth."""

import argparse
from fractions import Fraction as Q
import json
from math import gcd
from pathlib import Path

from analytic_sum_control import log_interval
from audit_primitive_normalization import outward_interval
from audit_smith_lattice import determinant, identity, matmul
from verify_adjacent_bridge import compound


def charpoly3(a):
    trace = sum(a[i][i] for i in range(3))
    second = sum(a[i][i]*a[j][j]-a[i][j]*a[j][i]
                 for i in range(3) for j in range(i+1, 3))
    return [-determinant(a), second, -trace, 1]


def evaluate(coefficients, x):
    result = 0
    for c in reversed(coefficients):
        result = c + x*result
    return result


def bisect_root(coefficients, lo, hi):
    assert evaluate(coefficients, lo)*evaluate(coefficients, hi) < 0
    for _ in range(80):
        mid = (lo+hi)/2
        if evaluate(coefficients, lo)*evaluate(coefficients, mid) <= 0:
            hi = mid
        else:
            lo = mid
    assert evaluate(coefficients, lo)*evaluate(coefficients, hi) <= 0
    return lo, hi


def verify(root):
    source = json.loads((root/'notes/pade-sign-recurrence-0.json').read_text())
    p = source['p']
    assert all(len(cs) == 26 for cs in p)
    a, b, c = [-Q(cs[-1], p[3][-1]) for cs in p[:3]]
    assert [a, b, c] == [729, -15146217, -30510]
    limit = [[0, 1, 0], [0, 0, 1], list(map(int, (a, b, c))) ]
    exterior = compound(limit)
    assert exterior == [[0, 0, 1], [-729, 0, -30510], [0, -729, 15146217]]
    pc = charpoly3(limit)
    pe = charpoly3(exterior)
    assert pc == [-729, 15146217, 30510, 1]
    assert pe == [-531441, -22241790, -15146217, 1]
    # Three disjoint sign-change intervals exhaust all three roots.
    intervals = [bisect_root(pe, Q(lo), Q(hi)) for lo, hi in
                 ((-2, -1), (-1, 0), (15146218, 15146219))]
    rho_lo, rho_hi = intervals[-1]
    log_lo = log_interval(rho_lo)[0]
    log_hi = log_interval(rho_hi)[1]

    # Integral conjugate after scaling the second compound by 27.
    diagonal = [[Q(1, 27), 0, 0], [0, 1, 0], [0, 0, 1]]
    inverse = [[27, 0, 0], [0, 1, 0], [0, 0, 1]]
    integral = [[0, 0, 1], [-1, 0, -1130], [0, -27, 560971]]
    recovered = matmul(matmul(diagonal, integral), inverse)
    assert exterior == [[27*x for x in row] for row in recovered]
    assert determinant(limit) == 3**6 and determinant(exterior) == 3**12
    reduction = [[divmod(x, 3)[1] for x in row] for row in integral]
    unit_row = [[0, 0, 1]]
    assert reduction[0] == reduction[2] == unit_row[0]
    assert matmul(unit_row, reduction) == unit_row

    powers, current = [], identity(3)
    for k in range(1, 21):
        current = matmul(limit, current)
        minors = compound(current)
        content = gcd(*(x for row in minors for x in row))
        assert content == 27**(k-1)
        powers.append({'power': k, 'second_determinantal_divisor': str(content)})

    # A spectral radius above 1000 can coexist with all Smith factors one.
    unimodular = [[1000, 1, 0], [999, 1, 0], [0, 0, 1]]
    assert determinant(unimodular) == 1
    assert charpoly3(unimodular) == [-1, 1002, -1002, 1]
    assert evaluate([1, -1001, 1], 1000) < 0
    assert evaluate([1, -1001, 1], 1001) > 0
    unit_powers, current = [], identity(3)
    for k in range(1, 13):
        current = matmul(unimodular, current)
        assert determinant(current) == 1
        content = gcd(*(x for row in compound(current) for x in row))
        assert content == 1
        unit_powers.append({'power': k, 'second_determinantal_divisor': 1})
    model_log = log_interval(Q(27))
    return {
        'scope': 'Exact limiting-operator characteristic polynomials and universal '
                 'paper counterexamples. Finite matrix checks support the derivations; '
                 'no identification of actual lattice growth with the constant model.',
        'limiting_transfer': limit, 'limiting_exterior_transfer': exterior,
        'transfer_charpoly_ascending': pc, 'exterior_charpoly_ascending': pe,
        'exterior_root_intervals': [outward_interval(lo, hi) for lo, hi in intervals],
        'exterior_log_spectral_radius_interval': outward_interval(log_lo, log_hi),
        'exterior_log_spectral_radius_per_original_index_interval':
            outward_interval(log_lo/2, log_hi/2),
        'scaled_integral_conjugate': integral,
        'conjugating_diagonal': ['1/27', '1', '1'],
        'constant_model_exact_divisor_formula': 'delta_2(A^k)=27^(k-1), k>=1',
        'constant_model_log_divisor_rate_per_original_index_interval':
            outward_interval(model_log[0]/2, model_log[1]/2),
        'constant_model_power_checks': powers,
        'unimodular_counterexample': unimodular,
        'unimodular_exterior_spectral_radius_interval': [1000, 1001],
        'unimodular_smith_factors_all_powers': [1, 1, 1],
        'unimodular_power_checks': unit_powers}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    data = verify(Path(__file__).resolve().parents[1])
    args.output.write_text(json.dumps(data, indent=2))
    print('Exterior characteristic polynomial:', data['exterior_charpoly_ascending'])
    print('Exterior log radius per original index:',
          data['exterior_log_spectral_radius_per_original_index_interval'])
    print('Constant-model arithmetic rate per original index:',
          data['constant_model_log_divisor_rate_per_original_index_interval'])
    print('Exact matrix and power checks passed.')


if __name__ == '__main__':
    main()
