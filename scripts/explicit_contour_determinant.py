"""Residue evaluations of the actual finite-moment and certified-tail determinant."""
from fractions import Fraction as Q
from math import lcm
from pathlib import Path
import json

from check_integral_cancellation import normalized_log_jet_coordinates
from integer_determinants import adjugate_column
from exact_transition_norm import weighted_profile
from parametric_odd_profiles import kernel
from check_dual_cost_reduction import reduce_binary_form


def poly(a,x):
    out=Q(0)
    for c in reversed(a):
        out=out*x+c
    return out


def construct(r,n):
    s=2*r+1; m=n-r; K=3*n; D=lcm(*range(1,n+1))**s
    blocks=[normalized_log_jet_coordinates(s,n,n-j) for j in range(r+1)]
    matrix=[[D*x for x in row] for row in zip(*blocks)]
    assert all(x.denominator==1 for row in matrix for x in row)
    matrix=[list(map(int,row)) for row in matrix]
    delta,a=adjugate_column(matrix,r-1)
    again,b=adjugate_column(matrix,r)
    assert delta==again and delta!=0
    u=weighted_profile(r,n,[Q(D*x,delta) for x in a])
    v=weighted_profile(r,n,[Q(D*x,delta) for x in b])
    atoms=[]
    for k in range(m+1,K+1):
        w=Q(k*(k+n),12*n*n)
        atoms.append((kernel(s,n,m,Q(k)),poly(u,w),poly(v,w)))
    last=kernel(s,n,m,Q(K))
    tails=[((r+1)*last*Q(K,4*r+1-4*i),u[i],v[i]) for i in range(r+1)]
    def exterior(x,y):
        return x[0]*y[0]*(x[1]*y[2]-x[2]*y[1])**2
    finite=sum((exterior(x,y) for i,x in enumerate(atoms) for y in atoms[i+1:]),Q(0))
    cross=sum((exterior(x,y) for x in atoms for y in tails),Q(0))
    tail=sum((exterior(x,y) for i,x in enumerate(tails) for y in tails[i+1:]),Q(0))
    all_atoms=atoms+tails
    A=sum((w*p*p for w,p,q in all_atoms),Q(0))
    B=sum((w*p*q for w,p,q in all_atoms),Q(0))
    C=sum((w*q*q for w,p,q in all_atoms),Q(0))
    det=A*C-B*B
    assert det==finite+cross+tail and min(finite,cross,tail)>=0 and det>0
    reduced,_,_=reduce_binary_form(A,B,C)
    alpha,_,nu=reduced
    mu=sum((x[0] for x in atoms),Q(0))+last*Q(K,4*r+1)
    scalar=mu*det/alpha
    assert scalar<=mu*nu<=Q(4,3)*scalar
    left,right=Q(1),Q(2)
    phase_derivative_numerator=lambda x: x**(s+1)*(x+2)-(x-1)*(x+1)**(s+1)
    assert phase_derivative_numerator(left)>0>phase_derivative_numerator(right)
    for _ in range(70):
        mid=(left+right)/2
        if phase_derivative_numerator(mid)>0:left=mid
        else:right=mid
    # The scalar second derivative is strictly negative on this bracket.
    assert (s-2)*right*(right+1)<2*(s+1)
    return {'weight':s,'index':n,'finite_double_residue_sum':str(finite),
            'mixed_tail_residue_sum':str(cross),'tail_determinant':str(tail),
            'actual_raw_determinant':str(det),
            'actual_reduced_first_coefficient':str(alpha),
            'scalar_sandwich_cost':str(scalar),
            'kernel_saddle_bracket':list(map(str,(left,right))),
            'kernel_hessian_negative_on_bracket':True}


def main():
    cases=[construct(r,n) for r,n in ((3,6),(3,12),(3,20),(4,8),(4,16),(5,10),(5,20),(6,12))]
    root=Path(__file__).resolve().parents[1]
    (root/'notes/explicit-contour-determinant.json').write_text(json.dumps({
        'cases':cases,'full_negative_rate_proved':False},indent=2))
    print(len(cases),'exact determinant residue evaluations and rational kernel-saddle brackets passed')


if __name__=='__main__':main()
