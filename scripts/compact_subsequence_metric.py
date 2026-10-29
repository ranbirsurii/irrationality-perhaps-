"""Exact finite compactness and covolume certificates; no equidistribution claim."""
from fractions import Fraction as Q
from pathlib import Path
import json
import sys


def main():
    sys.set_int_max_str_digits(200000)
    root=Path(__file__).resolve().parents[1]
    cases=json.loads((root/'notes/moment-metric-reduction.json').read_text())['cases']
    c=Q(1,100)
    rows=[]
    for case in cases:
        alpha,beta,nu=map(Q,case['reduced_gram'])
        det=alpha*nu-beta*beta
        R=Q(case['full_moment_bound'])
        assert det>0 and 0<alpha<=nu and 2*abs(beta)<=alpha
        minimum_squared=alpha*alpha/det
        compact=minimum_squared>=c*c
        volume_cost_squared=R*R*det/(nu*nu)
        if compact:
            assert R*R <= Q(16,9)/(c*c)*volume_cost_squared
        rows.append({'weight':case['weight'],'index':case['index'],
                     'normalized_minimum_squared':str(minimum_squared),
                     'threshold_met':compact,
                     'volume_cost_squared':str(volume_cost_squared)})
    (root/'notes/compact-subsequence-metric.json').write_text(json.dumps({
        'threshold':str(c),'cases':rows,'infinite_returns_proved':False,
        'volume_cost_limit_proved':False},indent=2))
    print(sum(x['threshold_met'] for x in rows),'of',len(rows),'finite compactness checks pass')


if __name__=='__main__':
    main()
