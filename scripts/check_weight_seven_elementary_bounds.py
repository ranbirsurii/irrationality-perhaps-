"""Global scalar saddle certificates and finite coefficient-height checks."""

from fractions import Fraction as Q
from pathlib import Path
import json
from math import comb, lcm

from analytic_sum_control import log_interval


def main():
    root=Path(__file__).resolve().parents[1]
    a=Q(25309,25000)
    y=a*(a+1)
    p=5*y**4-2*y**3-13*y*y-7*y-1
    assert p>0
    gap=(a+1)**8-2397*(a+2)**2*(a-1)
    assert gap>0
    budget=log_interval(Q(2397))
    assert budget[0]-7>Q('0.78')
    constant=12*5**14*3**38
    data=json.loads((root/'notes/weight-seven-combined-kernel.json').read_text(encoding='utf-8'))
    results=[]
    for row in data['cases']:
        n=row['index']
        d=lcm(*range(1,n+1))**7
        forms=[]
        for form in row['pair']:
            H=sum((abs(Q(c))*(12*n*n)**ell for ell,c in
                   enumerate(form['cubic_profile_coefficients'])),Q(0))
            bound=d*constant*(n+1)**16*H/Q(2397)**n
            coefficients=list(map(Q,form['cubic_profile_coefficients']))
            u0=(n-2)*(2*n-2)
            shifted=[sum((coefficients[j]*comb(j,k)*u0**(j-k)
                           for j in range(k,4)),Q(0)) for k in range(4)]
            sign_certificate=all(x>=0 for x in shifted) or all(x<=0 for x in shifted)
            lo,hi=map(Q,form['combined_sum_interval'])
            assert max(abs(lo),abs(hi))<=bound
            forms.append({'weighted_cubic_height':str(H),
                          'elementary_majorant':str(bound),
                          'majorant_below_one':bound<1,
                          'translated_cubic_has_common_coefficient_sign':sign_certificate,
                          'scope':'Finite check, not an eventual bound.'})
        results.append({'index':n,'forms':forms})
        print(n,'elementary bounds below one',[x['majorant_below_one'] for x in forms])
    result={'global_stationary_polynomial_coefficients':[-1,-7,-13,-2,5],
            'stationary_upper_endpoint':str(a),
            'stationary_positive_value':str(p),'base_2397_positive_gap':str(gap),
            'cost_budget_strictly_greater_than':'0.78','cases':results,
            'uniform_coefficient_height_bound_proved':False}
    (root/'notes/weight-seven-elementary-bounds.json').write_text(
        json.dumps(result,indent=2),encoding='utf-8')


if __name__=='__main__':
    main()
