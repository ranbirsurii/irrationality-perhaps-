"""Exact CM identification and cusp-cost comparison, without a limiting claim."""
from fractions import Fraction as Q
from math import gcd, lcm
from pathlib import Path
import json
import sys


def main():
    sys.set_int_max_str_digits(200000)
    root=Path(__file__).resolve().parents[1]
    source=json.loads((root/'notes/moment-metric-reduction.json').read_text())['cases']
    rows=[]
    for case in source:
        a,b,c=map(Q,case['reduced_gram'])
        d=a*c-b*b
        denominator=lcm(a.denominator,b.denominator,c.denominator)
        A,B,C=[int(x*denominator) for x in (a,b,c)]
        content=gcd(A,gcd(2*B,C))
        A,B,C=[x//content for x in (A,2*B,C)]
        assert gcd(A,gcd(B,C))==1
        assert A>0 and A<=C and abs(B)<=A
        discriminant=B*B-4*A*C
        x=-b/a
        y_squared=d/(a*a)
        assert x==-Q(B,2*A)
        assert y_squared==Q(-discriminant,4*A*A)
        assert abs(x)<=Q(1,2) and y_squared>=Q(3,4)
        assert x*x+y_squared==c/a>=1
        R=Q(case['full_moment_bound'])
        cusp=R*d/(a*c)
        assert cusp<=R<=Q(4,3)*cusp
        rows.append({'weight':case['weight'],'index':case['index'],
                     'primitive_CM_coefficients':list(map(str,(A,B,C))),
                     'CM_discriminant':str(discriminant),
                     'real_part':str(x),'imaginary_part_squared':str(y_squared),
                     'weighted_cusp_cost':str(cusp),
                     'full_to_cusp_ratio':str(R/cusp)})
    (root/'notes/modular-cusp-cost.json').write_text(json.dumps({
        'cases':rows,'cusp_cost_limit_proved':False},indent=2))
    print(len(rows),'exact CM and cusp-cost identities verified; no limit inferred')


if __name__=='__main__':
    main()
