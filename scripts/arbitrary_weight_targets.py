"""Certified thresholds of a sufficient target; no claim that the family meets them."""
from fractions import Fraction as Q
from pathlib import Path
import json
from gamma_epsilon_rates import logarithm
from audit_primitive_normalization import outward_interval


def main():
    a=logarithm(Q(2397));b=logarithm(Q(4));rows=[]
    for s in (7,9,11,13,15,21,51):
        lower=a[0]+(s-7)*b[0]-s
        upper=a[1]+(s-7)*b[1]-s
        assert lower>Q(3,4)
        rows.append({'weight':s,'allowed_cost_rate_interval':outward_interval(lower,upper),
                     'required_Gamma_over_lambda2_rate_threshold_interval':outward_interval(-upper,-lower),
                     'uniform_sufficient_cost_allowance':'3/4'})
        print(s,tuple(float(Q(x)) for x in rows[-1]['allowed_cost_rate_interval']))
    root=Path(__file__).resolve().parents[1]
    (root/'notes/arbitrary-weight-targets.json').write_text(json.dumps({
        'thresholds':rows,'actual_joint_bound_proved':False},indent=2))


if __name__=='__main__':main()
