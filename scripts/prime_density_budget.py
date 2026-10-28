"""Rigorous constants for a conditional prime-divisibility/lattice argument."""

import argparse
from fractions import Fraction as Q
import json
from math import isqrt
from pathlib import Path

from analytic_sum_control import log_interval
from audit_primitive_normalization import outward_interval


def atan_bounds(x, terms=80):
    total = sum(((-1)**k*x**(2*k+1)/(2*k+1) for k in range(terms)), Q(0))
    next_term = (-1)**terms*x**(2*terms+1)/(2*terms+1)
    return min(total, total+next_term), max(total, total+next_term)


def budget():
    a, b = atan_bounds(Q(1,5)), atan_bounds(Q(1,239))
    pi = (16*a[0]-4*b[1], 16*a[1]-4*b[0])
    scale = 10**40
    floor = isqrt(3*scale*scale)
    sqrt3 = (Q(floor,scale), Q(floor+1,scale))
    assert sqrt3[0]**2 < 3 < sqrt3[1]**2
    log3, log6 = log_interval(Q(3)), log_interval(Q(6))
    cg = (3+pi[0]/(4*sqrt3[1])+Q(3,4)*log3[0],
          3+pi[1]/(4*sqrt3[0])+Q(3,4)*log3[1])
    gamma = (Q(3,2)+Q(3,2)*log3[0], Q(3,2)+Q(3,2)*log3[1])
    normal = (5+3*log6[0]-cg[1], 5+3*log6[1]-cg[0])
    cost = (5+normal[0]/2-gamma[1], 5+normal[1]/2-gamma[0])
    margin = (Q(4970793,1000000)-cost[1], Q(4970794,1000000)-cost[0])
    assert margin[0] > Q(6,100)
    values = {'lower_column_divisor_constant':cg,'image_content_constant':gamma,
              'primitive_normal_upper_rate_constant':normal,
              'balanced_lattice_cost_constant':cost,
              'conditional_decay_margin':margin}
    return {'scope':'Rigorous constant enclosures. The lower-column divisor and '
                    'primitive-normal upper bounds have paper proofs. The pointwise '
                    'image-content candidate is false; an aggregate repair and '
                    'subexponential lattice shape are unproved.',
            'proof_status':{'lower_column_divisor_constant':'proved on paper',
                            'primitive_normal_upper_rate_constant':'proved on paper',
                            'image_content_constant':'reference constant; aggregate bound unproved',
                            'balanced_lattice_cost_constant':'conditional only'},
            'constants':{key:outward_interval(*interval) for key,interval in values.items()}}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',required=True,type=Path)
    args=parser.parse_args()
    result=budget()
    args.output.write_text(json.dumps(result,indent=2))
    for name,interval in result['constants'].items():
        print(name,tuple(float(Q(x)) for x in interval))


if __name__=='__main__':
    main()
