"""Track the actual Laurent map and joint moment cost of shorter numerators."""
from fractions import Fraction as Q
from math import comb, factorial, gcd, lcm
from pathlib import Path
import json
import sys

from check_integral_cancellation import harmonic, normalized_log_jet_coordinates
from saalschutz_kernel_transform import coefficients
from moment_metric_reduction import construct


def branch_a3(n,m,j):
    total=Q(0)
    for h in range(n+1):
        jet=[Q(1),Q(0),Q(0)]
        for v in range(2*m):
            c=Q(-h-m-j+v)
            jet=[c*jet[0],c*jet[1]+jet[0],c*jet[2]+jet[1]]
        e1=5*(harmonic(h,1)-harmonic(n-h,1))
        e2=(e1*e1+5*(harmonic(h,2)+harmonic(n-h,2)))/2
        total+=Q((-1)**h*comb(n,h)**5,factorial(2*m))*(jet[2]+jet[1]*e1+jet[0]*e2)
    return total


def main():
    sys.set_int_max_str_digits(200000)
    root=Path(__file__).resolve().parents[1]
    stored=json.loads((root/'notes/three-block-lattice-audit.json').read_text())['cases']
    transfers=[]
    for row in stored:
        n=row['index']
        if n not in (6,12,20,40):continue
        x=[int(rr[0]) for rr in row['cleared_coordinate_rows']]
        g=gcd(*x);H2=sum((v//g)**2 for v in x)
        blocks=[]
        D=lcm(*range(1,n+1))**5
        for i in range(3):
            m=n-i;c=coefficients(n,m)
            values=[branch_a3(n,m,j) for j in range(m+1)]
            actual=normalized_log_jet_coordinates(5,n,m)[0]
            assert sum((cj*a for cj,a in zip(c,values)),Q(0))==actual
            assert D*actual==x[i]
            blocks.append({'length':m,'multiplier_mass':str(sum(map(abs,c))),
                           'branch_laurent_maximum':str(max(map(abs,values)))})
        W=max(int(b['multiplier_mass']) for b in blocks)
        P=max(Q(b['branch_laurent_maximum']) for b in blocks)
        correct_square=3*Q(D,g)**2*W*W*P*P
        assert H2<=correct_square
        transfers.append({'index':n,'primitive_normal_squared':str(H2),
                          'maximum_multiplier_mass':str(W),
                          'H_squared_over_W_squared':str(Q(H2,W*W)),
                          'actual_map_upper_bound_squared':str(correct_square),'blocks':blocks})
        print('Laurent map',n,'H exceeds multiplier mass',H2>W*W,flush=True)
    choices=[]
    for r,n in ((3,20),(3,40),(4,24)):
        records=[]
        for length in sorted({r,n//2,3*n//4,n-2,n-1,n}):
            row=construct(r,n,length)
            records.append({'length':length,'complete_moment_cost':row['full_moment_bound']})
        best=min(records,key=lambda x:Q(x['complete_moment_cost']))
        choices.append({'weight':2*r+1,'index':n,'tested_lengths':records,'best_tested_length':best['length']})
        print('joint length budget',2*r+1,n,'best',best['length'],flush=True)
    (root/'notes/transform-height-transfer.json').write_text(json.dumps({
        'actual_laurent_map_checks':transfers,'joint_length_checks':choices,
        'new_H_rate_proved':False,'new_Gamma_rate_proved':False},indent=2))


if __name__=='__main__':main()
