"""Exact scalar certificates for the analytic rates, not sampled indices."""

from fractions import Fraction as Q
from pathlib import Path
import json

from analytic_sum_control import log_interval


def polynomial(x):
    y = x * (x + 1)
    return 3 * y ** 3 - 4 * y ** 2 - 5 * y - 1


def saddle_base(x):
    return (x + 2) ** 2 * (x - 1) / (x + 1) ** 6


def outward(lo, hi, scale=10 ** 12):
    a, b = lo * scale, hi * scale
    return [str(Q(a.numerator // a.denominator, scale)),
            str(Q((b.numerator + b.denominator - 1) // b.denominator, scale))]


def main():
    a = Q(1057, 1000)
    assert polynomial(a) * 1000 ** 6 == 54685013669880747
    assert 2057 ** 6 - 140 * 3057 ** 2 * 57 * 1000 ** 3 == 1178944474661131249
    lo, hi = Q(1), a
    for _ in range(80):
        mid = (lo + hi) / 2
        if polynomial(mid) < 0:
            lo = mid
        else:
            hi = mid
    scale = 10 ** 12
    lo_scaled, hi_scaled = lo * scale, hi * scale
    lo = Q(lo_scaled.numerator // lo_scaled.denominator, scale)
    hi = Q((hi_scaled.numerator + hi_scaled.denominator - 1) // hi_scaled.denominator, scale)
    assert polynomial(lo) < 0 < polynomial(hi)
    lower = log_interval(saddle_base(lo))[0]
    upper = log_interval(saddle_base(hi))[1]
    assert Q('-4.970794') < lower < upper < Q('-4.970793')
    log140 = log_interval(Q(140))
    log4 = log_interval(Q(4))
    budget_lo = log140[0] + 2 * log4[0] - 7
    budget_hi = log140[1] + 2 * log4[1] - 7
    assert Q('0.7142311') < budget_lo < budget_hi < Q('0.7142312')
    assert 5 + upper < Q('0.029207') < Q('0.03')
    assert 5 - log140[0] < Q('0.058358') < Q('0.06')
    result = {
        'scope': 'Global scalar saddle and rate certificates; no finite-index extrapolation.',
        'saddle_x_interval': [str(lo), str(hi)],
        'lambda5_outward_interval': outward(lower, upper),
        'lambda5_six_decimal_interval_proved': ['-4.970794', '-4.970793'],
        'weight7_coarse_cost_budget_interval': outward(budget_lo, budget_hi),
        'coarse_cofactor_upper_rate_less_than': '0.058358',
        'sharp_cofactor_upper_rate_less_than': '0.029207',
        'log_certificate': '32-term atanh series after powers-of-two reduction, with explicit geometric tail.'}
    destination = Path('publication/high-weight-criterion/analytic-rate-certificates.json')
    destination.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
