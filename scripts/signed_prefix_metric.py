"""Exact signed-prefix improvement, with a separately bounded infinite tail."""
from fractions import Fraction as Q
from math import factorial, gcd, lcm
from pathlib import Path
import json
import sys

from check_integral_cancellation import normalized_log_jet_coordinates
from integer_determinants import adjugate_column
from exact_transition_norm import weighted_profile
from parametric_odd_profiles import kernel
from check_dual_cost_reduction import reduce_binary_form
from moment_metric_reduction import pairing
from zeta_enclosure import euler_maclaurin_zeta_interval
from gamma_epsilon_rates import logarithm
from audit_primitive_normalization import outward_interval


def construct(r,n,multiple):
    s=2*r+1; m=n-r; K=int(multiple*n)
    assert K==multiple*n and K>m
    D=lcm(*range(1,n+1))**s
    blocks=[normalized_log_jet_coordinates(s,n,n-j) for j in range(r+1)]
    values=[[D*x for x in row] for row in zip(*blocks)]
    assert all(x.denominator==1 for row in values for x in row)
    M=[list(map(int,row)) for row in values]
    delta,a=adjugate_column(M,r-1)
    again,b=adjugate_column(M,r)
    assert delta==again and delta
    u=weighted_profile(r,n,[Q(x,delta) for x in a])
    v=weighted_profile(r,n,[Q(x,delta) for x in b])
    moments=[Q(0)]*(2*r+1)
    for k in range(m+1,K+1):
        term=kernel(s,n,m,Q(k)); w=Q(k*(k+n),12*n*n)
        power=Q(1)
        for j in range(2*r+1):
            moments[j]+=term*power; power*=w
    E=s*(n+1)-2*m; B=2*m*m+s*n*(n+1)
    exact_budget=s*sum((Q(K,K+j) for j in range(n+1)),Q(0))-m-sum(
        (Q(K,K-h) for h in range(1,m+1)),Q(0))
    power=exact_budget.numerator//exact_budget.denominator
    assert power>4*r+1 and power<=exact_budget
    last=kernel(s,n,m,Q(K))
    tail=[last*Q(1,12*n*n)**j*Q(K+n,K)**j*
          Q(K**(2*j+1),power-2*j-1) for j in range(2*r+1)]
    mass=moments[0]+tail[0]
    old=[[moments[i+j]+((r+1)*tail[2*i] if i==j else 0)
          for j in range(r+1)] for i in range(r+1)]
    new=[[moments[i]*moments[j]/moments[0]+
          ((r+1)*tail[2*i] if i==j else 0)
          for j in range(r+1)] for i in range(r+1)]
    old_gram=tuple(pairing(x,old,y) for x,y in ((u,u),(u,v),(v,v)))
    new_gram=tuple(pairing(x,new,y) for x,y in ((u,u),(u,v),(v,v)))
    diff=tuple(x-y for x,y in zip(old_gram,new_gram))
    assert diff[0]>=0 and diff[2]>=0 and diff[0]*diff[2]>=diff[1]**2
    old_red,_,_=reduce_binary_form(*old_gram)
    red,U,_=reduce_binary_form(*new_gram)
    old_cost=D*D*mass*old_red[2]; cost=D*D*mass*red[2]
    assert cost<=old_cost
    determinant=new_gram[0]*new_gram[2]-new_gram[1]**2
    scalar=D*D*mass*determinant/red[0]
    assert scalar<=cost<=Q(4,3)*scalar
    hh=tuple((r+1)*sum((x[i]*y[i]*tail[2*i] for i in range(r+1)),Q(0))
             for x,y in ((u,u),(u,v),(v,v)))
    prefixq=[sum((x[i]*moments[i] for i in range(r+1)),Q(0)) for x in (u,v)]
    assert determinant==hh[0]*hh[2]-hh[1]**2+(
        prefixq[0]**2*hh[2]-2*prefixq[0]*prefixq[1]*hh[1]+prefixq[1]**2*hh[0])/moments[0]
    prefix_row=[D*sum((x[i]*moments[i] for i in range(r+1)),Q(0)) for x in (u,v)]
    common=lcm(*(x.denominator for x in prefix_row))
    ints=[int(common*x) for x in prefix_row]; content=gcd(*ints)
    assert content>0
    aa,bb=[x//content for x in ints]; scale=Q(common,content)
    norm=aa*aa+bb*bb
    tail_trace=D*D*(r+1)*sum(((u[i]**2+v[i]**2)*tail[2*i] for i in range(r+1)),Q(0))
    bezout_cost=mass*(Q(1)/(scale*scale*moments[0])+tail_trace*norm)
    assert cost<=bezout_cost
    lo,hi=euler_maclaurin_zeta_interval(s,max(96,2*n))
    checks=[]
    for col in range(2):
        p,q=U[0][col],U[1][col]
        z=[p*x+q*y for x,y in zip(u,v)]
        exact_bound=D*D*mass*pairing(z,new,z)
        actual=max(abs(p*lo+q),abs(p*hi+q))
        assert actual**2<=exact_bound<=cost
        prefix=D*sum((z[i]*moments[i] for i in range(r+1)),Q(0))
        tail_energy=(r+1)*sum((z[i]**2*tail[2*i] for i in range(r+1)),Q(0))
        residual=max(abs(p*lo+q-prefix),abs(p*hi+q-prefix))
        assert residual**2<=D*D*tail[0]*tail_energy
        checks.append({'pair':[str(p),str(q)],'bound_squared':str(exact_bound),
                       'bound_below_one':exact_bound<1,
                       'direct_tail_residual_check':True})
    lr=logarithm(cost)
    excluded_digits=0
    while cost*10**(2*(excluded_digits+1))<1:
        excluded_digits+=1
    result={'weight':s,'index':n,'cutoff_multiple':str(multiple),'tail_power':power,
            'old_cost_squared':str(old_cost),'signed_prefix_cost_squared':str(cost),
            'improvement_factor':str(old_cost/cost),
            'log_cost_squared_per_index':outward_interval(lr[0]/n,lr[1]/n),
            'explicit_prefix_bezout_cost_squared':str(bezout_cost),
            'prefix_primitive_integer_norm_squared':str(norm),
            'prefix_scale':str(scale),
            'scalar_sandwich_lower':str(scalar),
            'cost_over_scalar':str(cost/scalar),
            'rank_one_update_identity_verified':True,
            'excludes_rational_denominators_at_most_power_of_ten':excluded_digits,
            'forms':checks,'exact_psd_improvement':True}
    if (r,n,multiple)==(3,8,Q(6)):
        export_integer_certificate(M,delta,a,b,U,mass,new_gram,red,cost)
    print(s,n,multiple,'log squared cost / n',float(sum(lr,Q(0))/(2*n)),
          'improvement',float(old_cost/cost),flush=True)
    return result


def export_integer_certificate(M,delta,a,b,U,mu,gram,reduced,cost):
    root=Path(__file__).resolve().parents[1]
    from symmetric_pade_audit import poised_period_coordinates
    clearing=lcm(*range(1,9))**7
    independently_computed=[[
        clearing*Q(factorial(8)**7,factorial(8-j)**2)*x
        for x in poised_period_coordinates(3,8,8-j)] for j in range(4)]
    assert [list(x) for x in zip(*independently_computed)]==M
    rows=['import OddZeta.PrimitivePairNormalization',
          'import Mathlib.Data.Fin.VecNotation','',
          'namespace OddZeta','',
          'def certificateDot4 (x y : Fin 4 → ℤ) : ℤ :=',
          '  x 0*y 0+x 1*y 1+x 2*y 2+x 3*y 3','']
    for i,row in enumerate(M):
        rows.append(f'def sevenEightRow{i} : Fin 4 → ℤ := ![{", ".join(map(str,row))}]')
    defs=['certificateDot4']+[f'sevenEightRow{i}' for i in range(4)]
    pairs=[]
    for col in range(2):
        p,q=U[0][col],U[1][col]
        vec=[Q(p*x+q*y,delta) for x,y in zip(a,b)]
        h=lcm(*(x.denominator for x in vec)); w=[int(h*x) for x in vec]
        assert [sum(x*y for x,y in zip(row,w)) for row in M]==[0,0,h*p,h*q]
        assert gcd(p,q)==1
        i=col+1; pairs.append((p,q))
        rows.extend([f'def sevenEightWeight{i} : Fin 4 → ℤ := ![{", ".join(map(str,w))}]',
                     f'def sevenEightContent{i} : ℤ := {h}',
                     f'def sevenEightP{i} : ℤ := {p}',f'def sevenEightQ{i} : ℤ := {q}'])
        local=[f'sevenEightWeight{i}',f'sevenEightContent{i}',f'sevenEightP{i}',f'sevenEightQ{i}']
        rows.extend(['',f'theorem seven_eight_integer_lift_{i} :',
                     f'    certificateDot4 sevenEightRow0 sevenEightWeight{i}=0 ∧',
                     f'    certificateDot4 sevenEightRow1 sevenEightWeight{i}=0 ∧',
                     f'    certificateDot4 sevenEightRow2 sevenEightWeight{i}=sevenEightContent{i}*sevenEightP{i} ∧',
                     f'    certificateDot4 sevenEightRow3 sevenEightWeight{i}=sevenEightContent{i}*sevenEightQ{i} := by',
                     '  decide','',
                     f'theorem seven_eight_primitive_{i} : Int.gcd sevenEightP{i} sevenEightQ{i}=1 := by',
                     '  decide','',
                     f'theorem seven_eight_exact_content_{i} :',
                     f'    Int.gcd (certificateDot4 sevenEightRow2 sevenEightWeight{i})',
                     f'      (certificateDot4 sevenEightRow3 sevenEightWeight{i})=sevenEightContent{i}.natAbs := by',
                     '  decide',''])
    determinant=pairs[0][0]*pairs[1][1]-pairs[1][0]*pairs[0][1]
    assert abs(determinant)==1
    rows.extend(['theorem seven_eight_pair_determinant :',
                 f'    sevenEightP1*sevenEightQ2-sevenEightP2*sevenEightQ1={determinant} := by',
                 '  norm_num [sevenEightP1,sevenEightP2,sevenEightQ1,sevenEightQ2]','',
                 'theorem seven_eight_pair_nonvanishing (x : ℝ) :',
                 '    (sevenEightP1:ℝ)*x+sevenEightQ1 ≠ 0 ∨',
                 '      (sevenEightP2:ℝ)*x+sevenEightQ2 ≠ 0 := by',
                 '  have hd : sevenEightP1*sevenEightQ2-sevenEightP2*sevenEightQ1 ≠ 0 := by',
                 '    rw [seven_eight_pair_determinant]', '    norm_num',
                 '  have h := integral_normalized_pair_nonvanishing',
                 '    sevenEightP1 sevenEightP2 sevenEightQ1 sevenEightQ2 1 1 x',
                 '    (one_dvd _) (one_dvd _) (one_dvd _) (one_dvd _)',
                 '    (by norm_num) (by norm_num) hd',
                 '  simpa using h',''])
    rat=lambda x:f'({x.numerator} : ℚ)/{x.denominator}'
    for name,value in zip(('A','B','C'),gram):
        rows.append(f'def sevenEightMetric{name} : ℚ := {rat(value)}')
    for name,value in zip(('Alpha','Beta','Nu'),reduced):
        rows.append(f'def sevenEightReduced{name} : ℚ := {rat(value)}')
    rows.extend([f'def sevenEightMass : ℚ := {rat(mu)}',
                 f'def sevenEightClearing : ℚ := {lcm(*range(1,9))**7}','',
                 'theorem seven_eight_metric_reduction :',
                 '    sevenEightMetricA*sevenEightP1^2+2*sevenEightMetricB*sevenEightP1*sevenEightQ1+',
                 '      sevenEightMetricC*sevenEightQ1^2=sevenEightReducedAlpha ∧',
                 '    sevenEightMetricA*sevenEightP1*sevenEightP2+',
                 '      sevenEightMetricB*(sevenEightP1*sevenEightQ2+sevenEightP2*sevenEightQ1)+',
                 '      sevenEightMetricC*sevenEightQ1*sevenEightQ2=sevenEightReducedBeta ∧',
                 '    sevenEightMetricA*sevenEightP2^2+2*sevenEightMetricB*sevenEightP2*sevenEightQ2+',
                 '      sevenEightMetricC*sevenEightQ2^2=sevenEightReducedNu := by',
                 '  norm_num [sevenEightMetricA,sevenEightMetricB,sevenEightMetricC,',
                 '    sevenEightP1,sevenEightP2,sevenEightQ1,sevenEightQ2,',
                 '    sevenEightReducedAlpha,sevenEightReducedBeta,sevenEightReducedNu]','',
                 'theorem seven_eight_metric_small :',
                 '    sevenEightClearing^2*sevenEightMass*sevenEightReducedNu < (1:ℚ)/10^38 := by',
                 '  norm_num [sevenEightClearing,sevenEightMass,sevenEightReducedNu]','',
                 'end OddZeta',''])
    (root/'OddZeta/WeightSevenIntegerCertificate.lean').write_text('\n'.join(rows),encoding='utf-8')


def main():
    sys.set_int_max_str_digits(200000)
    cases=[construct(r,n,c) for r,n in ((3,8),(3,12),(3,20),(3,40),(3,80),(3,160),(4,12),(5,12))
           for c in (Q(5,4),Q(3,2),Q(2),Q(3),Q(6))]
    root=Path(__file__).resolve().parents[1]
    (root/'notes/signed-prefix-metric.json').write_text(json.dumps({
        'cases':cases,'uniform_cost_rate_proved':False,
        'scope':'Exact finite signed-prefix metrics with analytic infinite-tail bounds; no limiting inference.'},indent=2))


if __name__=='__main__':main()
