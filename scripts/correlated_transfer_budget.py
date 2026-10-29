"""Exact correlated rate budget after the signed Laurent transfer."""
from fractions import Fraction as Q
from math import gcd,lcm
from pathlib import Path
import json,sys
from gamma_epsilon_rates import logarithm
from audit_primitive_normalization import outward_interval


def main():
    sys.set_int_max_str_digits(200000)
    root=Path(__file__).resolve().parents[1]
    rows=[]
    for row in json.loads((root/'notes/three-block-lattice-audit.json').read_text())['cases']:
        n=row['index']; x=[int(rr[0]) for rr in row['cleared_coordinate_rows']]
        a,b=([int(v) for v in rr] for rr in row['saturated_gauss_basis'])
        A,B,C=sum(v*v for v in a),sum(v*w for v,w in zip(a,b)),sum(v*v for v in b)
        g=gcd(*x);X=sum(v*v for v in x);N=X//(g*g)
        assert A*C-B*B==N and 3*A*C<=4*N
        G=int(row['kernel_image_content']);J=G*G*g*g*A
        transfer=Q(X,x[0]*x[0])
        d=lcm(*range(1,n+1))
        cost_square=Q(d**10*X,J)
        angle=Q(A*C,N)
        assert 1<=angle<=Q(4,3)
        # Fourth powers avoid every irrational square root.
        exact_core_fourth=Q(d**20*C*N,G**4*A)
        assert exact_core_fourth==cost_square**2*angle
        lj=logarithm(Q(J));lt=logarithm(transfer);lc=logarithm(cost_square)
        rows.append({'index':n,
            'relative_signed_transfer_rate_interval':outward_interval(*(v/(2*n) for v in lt)),
            'joint_Gamma_g_lambda1_rate_interval':outward_interval(*(v/(2*n) for v in lj)),
            'joint_core_cost_rate_interval':outward_interval(*(v/(2*n) for v in lc)),
            'angular_fourth_power_correction':str(angle)})
    left,right=Q(30005),Q(30006)
    f=lambda z:z**3-30510*z*z+15146217*z+729
    assert f(left)<0<f(right)
    for _ in range(80):
        mid=(left+right)/2
        if f(mid)<0:left=mid
        else:right=mid
    ell=(logarithm(left)[0]/2,logarithm(right)[1]/2)
    decay=(Q(4970793860341,10**12),Q(4970793860358,10**12))
    threshold=(10+ell[0]-decay[1],10+ell[1]-decay[0])
    cg=tuple(map(Q,json.loads((root/'notes/prime-density-budget.json').read_text())['constants']['lower_column_divisor_constant']))
    remaining=(threshold[0]-cg[1],threshold[1]-cg[0])
    (root/'notes/correlated-transfer-budget.json').write_text(json.dumps({
        'cases':rows,'full_joint_threshold_interval':outward_interval(*threshold),
        'sufficient_Gamma_lambda1_threshold_interval':outward_interval(*remaining),
        'required_joint_arithmetic_lower_bound_proved':False},indent=2))
    print('joint threshold',tuple(float(v) for v in threshold))
    print('sufficient Gamma*lambda1 threshold',tuple(float(v) for v in remaining))
    print(len(rows),'exact correlation identities verified; no asymptotic arithmetic lower bound inferred')


if __name__=='__main__':main()
