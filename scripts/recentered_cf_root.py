"""Recenter a signed-prefix interval and retain the previous integer pair."""
from fractions import Fraction as Q
from math import gcd,lcm
from pathlib import Path
import json
from check_integral_cancellation import normalized_log_jet_coordinates
from integer_determinants import adjugate_column
from cf_root_compression import certify,best_pair,convergent_pairs,rational_log
from zeta_enclosure import euler_maclaurin_zeta_interval


def pair_bound(pair,center,radius):
    return max(abs(q*center-p)+q*radius for p,q in pair)


def check(s,n):
    r=(s-1)//2;D=lcm(*range(1,n+1))**s
    cols=[normalized_log_jet_coordinates(s,n,n-j) for j in range(r+1)]
    assert all((D*c[i]).denominator==1 for c in cols for i in range(r+1))
    B=[[int(D*c[i]) for c in cols] for i in range(r+1)]
    det,U=adjugate_column(B,r-1);_,V=adjugate_column(B,r)
    roots=[]
    for u,v in zip(U,V):
        if not v:continue
        g=gcd(u,v);roots.append((-v//g,u//g))
    p0,q0=min(roots,key=lambda pair:max(map(abs,pair)))
    rootR,K,_,_,prefix,tail=certify(s,n,U,V,det,D,p0,q0,Q(1,4**n))
    rootR=max(rootR,Q(1,4**n))
    oldcenter=Q(-q0,p0);oldradius=rootR/abs(p0)
    newcenter=(prefix-q0)/p0;newradius=tail/abs(p0)
    assert newradius>0
    assert abs(newcenter-oldcenter)+newradius<=oldradius
    zl,zh=euler_maclaurin_zeta_interval(s,96)
    assert newcenter-newradius<=zl<=zh<=newcenter+newradius
    oldE,oldpair,_,_=best_pair(oldcenter,oldradius)
    candidates=[(pair_bound(oldpair,newcenter,newradius),oldpair)]
    candidates += [(pair_bound(pair,newcenter,newradius),pair)
                   for pair in convergent_pairs(newcenter)]
    newE,pair=min(candidates,key=lambda item:item[0])
    assert 0<newE<=pair_bound(oldpair,newcenter,newradius)<=oldE
    assert newE*8**n<oldE
    eta=min(newE/16,Q(1,8*sum(q for p,q in pair)))
    certified=[]
    for Pj,Qj in pair:
        R,Kc,nonzero,prefix_nonzero,_,_=certify(s,n,U,V,det,D,Qj,-Pj,eta)
        assert R<=Q(9,8)*newE
        certified.append({'pair':[str(Qj),str(-Pj)],'majorant':str(R),
            'cutoff':Kc,'finite_nonzero':nonzero,'signed_prefix_excludes_zero':prefix_nonzero})
    assert any(e['signed_prefix_excludes_zero'] for e in certified)
    assert abs(pair[0][0]*pair[1][1]-pair[1][0]*pair[0][1])==1
    common=max(Q(e['majorant']) for e in certified)
    if s==7:
        thresholds={6:Q(3,10**14),8:Q(7,10**27),12:Q(5,10**37),
                    16:Q(4,10**49),20:Q(3,10**77)}
        assert common<thresholds[n]
    return {'weight':s,'index':n,'original_bound':str(oldE),'recentered_bound':str(newE),
        'original_radius':str(oldradius),'recentered_radius':str(newradius),
        'interval_refinement_verified':True,'original_pair_retained':True,
        'selected_original_pair':pair==oldpair,'finite_gain_at_least_log8':True,
        'finite_epsilon_gain':rational_log(oldE/newE)/n,
        'recentered_accuracy_rate_finite':-rational_log(newradius)/n,
        'certified_common_majorant':str(common),'certificates':certified}


def rational_controls():
    alpha=Q(3,2)
    for n in range(1,13):
        radius=Q(1,10**n);oldcenter=alpha+radius
        newcenter=alpha+radius/2;newradius=radius/2
        assert abs(newcenter-oldcenter)+newradius==radius
        oldE,oldpair,_,_=best_pair(oldcenter,radius)
        pairs=[oldpair]+list(convergent_pairs(newcenter))
        newE,pair=min(((pair_bound(pair,newcenter,newradius),pair) for pair in pairs),
                     key=lambda item:item[0])
        assert newE<=oldE
        assert newE>=max(abs(q*alpha-p) for p,q in pair)>=Q(1,2)
    return 12


def main():
    cases=[check(s,n) for s,n in ((7,6),(7,8),(7,12),(7,16),(7,20),
                                  (9,8),(9,12),(9,16),(11,10),(11,14))]
    path=Path(__file__).resolve().parents[1]/'notes/recentered-cf-root.json'
    path.write_text(json.dumps({'cases':cases,'rational_negative_controls':rational_controls(),
                               'uniform_epsilon_gain_proved':False},indent=2))
    for c in cases:print(c['weight'],c['index'],'bound',float(Q(c['certified_common_majorant'])),
        'finite epsilon gain',round(c['finite_epsilon_gain'],5))
    print(len(cases),'nested intervals and',3*len(cases),'signed-prefix certificates passed')


if __name__=='__main__':main()
