"""Compress cofactor-root heights and certify independent primitive form pairs."""
from fractions import Fraction as Q
from math import gcd,lcm,log
from pathlib import Path
import json
from check_integral_cancellation import normalized_log_jet_coordinates
from integer_determinants import adjugate_column
from adjugate_signed_prefix import kernel,filter_polynomial,tail_bound
from weight_seven_combined_kernel import evaluate
from zeta_enclosure import euler_maclaurin_zeta_interval


def certify(s,n,U,V,det,D,p,q,eta):
    r=(s-1)//2;m0=n-r
    assert gcd(p,q)==1 and eta>0
    w=[p*u+q*v for u,v in zip(U,V)]
    H=filter_polynomial(s,n,w,det,D);K=n+1
    while tail_bound(s,n,H,K)>eta:K*=2
    tail=tail_bound(s,n,H,K)
    prefix=sum((kernel(s,n,m0,Q(t))*evaluate(H,Q(t*(t+n)))
                for t in range(m0+1,K+1)),Q(0))
    R=abs(prefix)+tail
    zl,zh=euler_maclaurin_zeta_interval(s,96)
    lo,hi=sorted((p*zl+q,p*zh+q))
    assert prefix-tail<=lo<=hi<=prefix+tail
    assert max(abs(lo),abs(hi))<=R
    return R,K,lo*hi>0,abs(prefix)>tail,prefix,tail


def convergent_pairs(sigma):
    num,den=sigma.numerator,sigma.denominator
    p0,p1,q0,q1=0,1,1,0;previous=(1,0)
    while den:
        a,rem=divmod(num,den)
        p,q=a*p1+p0,a*q1+q0
        assert abs(previous[0]*q-p*previous[1])==1
        assert q>0 and gcd(p,q)==1
        V=max(q,previous[1])
        assert all(abs(Qi*sigma-Pi)<=Q(1,V) for Pi,Qi in (previous,(p,q)))
        yield previous,(p,q)
        previous=p,q;p0,p1,q0,q1=p1,p,q1,q;num,den=den,rem


def rational_log(x):return log(x.numerator)-log(x.denominator)


def best_pair(sigma,delta):
    assert delta>0
    best=None;steps=0
    for pair in convergent_pairs(sigma):
        E=max(abs(Qi*sigma-Pi)+Qi*delta for Pi,Qi in pair)
        assert E>0
        if best is None or E<best[0]:best=E,pair,steps
        steps+=1
    return (*best,steps)


def controls():
    for n in range(1,13):
        alpha=Q(3,2);delta=Q(1,10**n);sigma=alpha+delta
        E,pair,_,_=best_pair(sigma,delta)
        actual=max(abs(Qi*alpha-Pi) for Pi,Qi in pair)
        assert E>=actual>=Q(1,2)
    P,Qd=1,1
    for _ in range(16):
        assert abs(P*P-2*Qd*Qd)==1
        E,_,_,_=best_pair(Q(P,Qd),Q(1,2*Qd*Qd))
        assert E<=Q(3,2*Qd)
        P,Qd=P+2*Qd,P+Qd
    return {'rational_negative_controls':12,'pell_positive_controls':16}


def check(s,n):
    r=(s-1)//2;D=lcm(*range(1,n+1))**s
    cols=[normalized_log_jet_coordinates(s,n,n-j) for j in range(r+1)]
    assert all((D*c[i]).denominator==1 for c in cols for i in range(r+1))
    B=[[int(D*c[i]) for c in cols] for i in range(r+1)]
    det,U=adjugate_column(B,r-1);_,V=adjugate_column(B,r)
    roots=[]
    for u,v in zip(U,V):
        if not v:continue
        g=gcd(u,v);p=-v//g;q=u//g
        roots.append((p,q))
    p0,q0=min(roots,key=lambda pair:max(map(abs,pair)))
    rootR,rootK,_,_,_,_=certify(s,n,U,V,det,D,p0,q0,Q(1,4**n))
    rootR=max(rootR,Q(1,4**n))
    sigma=Q(-q0,p0);delta=rootR/abs(p0)
    zl,zh=euler_maclaurin_zeta_interval(s,96)
    assert sigma-delta<=zl<=zh<=sigma+delta
    E,pair,selected,steps=best_pair(sigma,delta)
    height=max(q for p,q in pair)
    assert E<=Q(1,height)+height*delta
    certified=[]
    eta=min(E/16,Q(1,8*sum(Qi for Pi,Qi in pair)))
    for Pj,Qj in pair:
        p,q=Qj,-Pj
        R,K,nonzero,prefix_nonzero,_,_=certify(s,n,U,V,det,D,p,q,eta)
        assert R<=Q(9,8)*E
        certified.append({'pair':[str(p),str(q)],'signed_majorant':str(R),
                          'cutoff':K,'finite_nonzero':nonzero,
                          'signed_prefix_excludes_zero':prefix_nonzero})
    assert any(c['signed_prefix_excludes_zero'] for c in certified)
    determinant=pair[0][0]*pair[1][1]-pair[1][0]*pair[0][1]
    assert abs(determinant)==1
    common=max(Q(e['signed_majorant']) for e in certified)
    finite_thresholds={6:Q(9,10**9),8:Q(2,10**12),12:Q(4,10**21),
                       16:Q(8,10**30),20:Q(3,10**37)}
    if s==7:assert common<finite_thresholds[n]
    return {'weight':s,'index':n,'root_accuracy_upper_bound':str(delta),
        'root_accuracy_rate_finite':-rational_log(delta)/n,'root_form_majorant':str(rootR),
        'continued_fraction_steps':steps,'selected_pair_index':selected,
        'maximum_convergent_denominator':str(height),'unimodular_determinant':determinant,
        'pair_upper_bound':str(E),'certified_common_majorant':str(common),
        'common_decay_rate_finite':-rational_log(common)/n,'certificates':certified}


def main():
    cases=[check(s,n) for s,n in ((7,6),(7,8),(7,12),(7,16),(7,20),
                                  (9,8),(9,12),(9,16),(11,10),(11,14))]
    path=Path(__file__).resolve().parents[1]/'notes/cf-root-compression.json'
    path.write_text(json.dumps({'cases':cases,'controls':controls(),
                               'uniform_decay_proved':False},indent=2))
    for c in cases:
        print(c['weight'],c['index'],'common bound',float(Q(c['certified_common_majorant'])),
              'finite accuracy rate',round(c['root_accuracy_rate_finite'],5))
    print(len(cases),'unimodular pairs;',3*len(cases),'signed-prefix certificates passed')


if __name__=='__main__':main()
