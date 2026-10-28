"""Enclose constants in the proved row-balance and conditional shape budget."""

import json
from fractions import Fraction as Q
from pathlib import Path

from analytic_sum_control import log_interval
from audit_primitive_normalization import outward_interval


def main():
    root = Path(__file__).resolve().parents[1]
    data = json.loads((root/'notes/prime-density-budget.json').read_text())['constants']
    cg = tuple(map(Q, data['lower_column_divisor_constant']))
    gamma = tuple(map(Q, data['image_content_constant']))
    ell = (log_interval(Q(30005))[0]/2, log_interval(Q(30006))[1]/2)
    normal = (5+ell[0]-cg[1], 5+ell[1]-cg[0])
    cost = (5+normal[0]/2-gamma[1], 5+normal[1]/2-gamma[0])
    log140 = log_interval(Q(140))
    margin = (log140[0]-cost[1], log140[1]-cost[0])
    assert cost[1]+Q(3, 20) < log140[0]
    values = {'raw_coefficient_rate': ell,
              'primitive_normal_upper_rate_bound': normal,
              'conditional_balanced_cost_rate': cost,
              'conditional_margin_vs_log140': margin,
              'sufficient_kappa_rate_threshold': (2*margin[0], 2*margin[1])}
    output = {'scope': 'Exact constant enclosures using the proved row-balance recurrence. '
              'The normal upper rate uses the paper-proved lower-column divisor. '
              'The content rate for Gamma and the required kappa upper rate are unproved.',
              'constants': {name: outward_interval(*value) for name, value in values.items()}}
    (root/'notes/row-balance-rate-budget.json').write_text(
        json.dumps(output, indent=2), encoding='utf-8')
    print('Constant enclosures saved. A kappa rate at most 0.30 is sufficient '
          'conditional on the unproved content estimate.')


if __name__ == '__main__':
    main()
