"""Exact shared-parameter odd-weight construction, without a growth assumption."""

from fractions import Fraction as Q
from math import factorial, gcd, lcm, prod
from pathlib import Path
import json

from check_integral_cancellation import normalized_log_jet_coordinates
from check_dual_cost_reduction import dot, reduce_binary_form
from integer_determinants import adjugate_column, bareiss
from weight_seven_combined_kernel import multiply, evaluate
from zeta_enclosure import euler_maclaurin_zeta_interval


def kernel(s,n,m,t):
    return Q(factorial(n)**s,factorial(m)**2)*prod(
        (t-h)*(t+n+h) for h in range(1,m+1))/prod((t+h)**s for h in range(n+1))


def construct(r,n,B=None):
    B=n if B is None else B
    assert r>=2 and n>=2*r and n%2==0 and r<=B<=n
    s=2*r+1; D=lcm(*range(1,n+1))**s; m0=B-r
    blocks=[normalized_log_jet_coordinates(s,n,B-j) for j in range(r+1)]
    M=[[D*x for x in row] for row in zip(*blocks)]
    assert all(x.denominator==1 for row in M for x in row)
    M=[list(map(int,row)) for row in M]
    delta,a=adjugate_column(M,r-1)
    again,b=adjugate_column(M,r)
    assert delta==again
    reduced,U,steps=reduce_binary_form(dot(a,a),dot(a,b),dot(b,b))
    F=(factorial(B)//factorial(m0))**2
    columns=[]; scales=[]
    for j in range(r+1):
        polynomial=[Q(1)]
        for h in range(m0+1,B-j+1):
            polynomial=multiply(polynomial,[-h*(n+h),1])
        scale=(factorial(B)//factorial(B-j))**2
        scales.append(scale)
        columns.append([int(scale*x) for x in polynomial]+[0]*j)
    R=[list(row) for row in zip(*columns)]
    assert bareiss(R)==(-1)**(r*(r+1)//2)*prod(scales)
    cutoff=3*n
    exponent=s*(n+1)-2*m0-(2*r+2)
    assert cutoff*exponent>=2*m0*m0+s*n*(n+1)
    term=kernel(s,n,m0,Q(m0+1)); peak=term
    for k in range(m0+1,cutoff):
        term*=Q(k**(s+1)*(k+n+m0+1),(k-m0)*(k+n+1)**(s+1))
        peak=max(peak,term)
    assert term==kernel(s,n,m0,Q(cutoff))
    moment_bound=3*n*peak+(3*n+1)*term
    forms=[]
    for col in range(2):
        p,q=U[0][col],U[1][col]
        v=[Q(p*x+q*y,delta) for x,y in zip(a,b)]
        assert [sum(x*y for x,y in zip(row,v)) for row in M]==[0]*(r-1)+[p,q]
        t=lcm(*(x.denominator for x in v)); w=[int(t*x) for x in v]
        assert gcd(t*p,t*q)==t
        x=[int(delta*z) for z in v]
        numerator_coefficients=[sum(z*y for z,y in zip(row,x)) for row in R]
        coefficients=[Q(z,F*delta) for z in numerator_coefficients]
        J=sum((abs(z)*(12*n*n)**ell for ell,z in enumerate(coefficients)),Q(0))
        mass=sum(map(abs,v)); gx=gcd(*x); gb=gcd(*numerator_coefficients)
        upper_factor=56**r if B==n else (14*n*n)**r
        assert mass<=J<=upper_factor*mass
        assert gb%gx==0 and F%(gb//gx)==0
        majorant=D*J*moment_bound
        zlo,zhi=euler_maclaurin_zeta_interval(s,96)
        assert max(abs(p*zlo+q),abs(p*zhi+q))<=majorant
        for k in (Q(B-r+1),Q(n+1),Q(3*n),Q(2*n+1,2)):
            actual=sum((v[j]*kernel(s,n,B-j,k) for j in range(r+1)),Q(0))
            assert actual==kernel(s,n,m0,k)*evaluate(coefficients,k*(k+n))
            assert kernel(s+2,n,m0,k)==kernel(s,n,m0,k)*(
                Q(factorial(n),1)/prod(k+h for h in range(n+1)))**2
        forms.append({'integer_coefficient_pair':list(map(str,(p,q))),
                      'integer_kernel_vector':list(map(str,w)),
                      'exact_coefficient_gcd':str(t),
                      'profile_coefficients':list(map(str,coefficients)),
                      'weighted_height':str(J),'height_mass_comparison_verified':True,
                      'elementary_joint_moment_majorant':str(majorant),
                      'content_quotient_divides_F':True})
    return {'r':r,'weight':s,'index':n,'numerator_length':B,
            'profile_degree':r,'gauss_steps':steps,
            'frame_determinant':str(bareiss(R)),'forms':forms,
            'scope':'Exact finite checks of the shared-parameter construction; no all-index growth inference.'}


def main():
    data=[]
    for r,n in ((3,6),(3,8),(4,8),(4,12),(5,10),(5,12),(6,12)):
        row=construct(r,n);data.append(row)
        print('weight',2*r+1,'index',n,'profile degree',r,'verified',flush=True)
    alternatives=[]
    for r,n,choices in ((2,8,(4,8)),(3,12,(3,6,9,12)),
                         (3,20,(5,10,15,20)),(4,12,(4,6,9,12)),
                         (5,12,(5,6,9,12))):
        for B in choices:
            alternatives.append(construct(r,n,B))
            print('alternative weight',2*r+1,'index',n,'numerator length',B,'verified',flush=True)
    destination=Path(__file__).resolve().parents[1]/'notes/parametric-odd-profiles.json'
    selections=[]
    for r,n in sorted({(x['r'],x['index']) for x in alternatives}):
        choices=[x for x in alternatives if x['r']==r and x['index']==n]
        best=min(choices,key=lambda x:max(Q(f['elementary_joint_moment_majorant']) for f in x['forms']))
        selections.append({'weight':2*r+1,'index':n,'selected_numerator_length':best['numerator_length'],
                           'selection_scope':'Minimum among the explicitly checked lengths only.'})
        print('joint-budget selection',2*r+1,n,best['numerator_length'],flush=True)
    destination.write_text(json.dumps({'cases':data,'alternative_length_cases':alternatives,
                                      'finite_joint_budget_selections':selections,
                                      'uniform_growth_proved':False},indent=2),encoding='utf-8')


if __name__=='__main__':
    main()
