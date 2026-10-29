"""Rational enclosures for the exact multiplier entropy, not for CF digits."""
from fractions import Fraction as Q
from math import comb,isqrt
from pathlib import Path
import json,sys
from gamma_epsilon_rates import logarithm
from audit_primitive_normalization import outward_interval


def entropy(beta):
    scale=10**30;d=(1+2*beta)*scale*scale
    root=isqrt(d.numerator//d.denominator)
    lo,hi=Q(root,scale),Q(root+1,scale)
    tl=beta/(1+beta+hi);tu=beta/(1+beta+lo)
    l1,u1=logarithm(1+tl),logarithm(1+tu)
    lm,um=logarithm(1-tl),logarithm(1-tu)
    lt,ut=logarithm(tl),logarithm(tu)
    return ((1+2*beta)*l1[0]-lm[1]-beta*ut[1],
            (1+2*beta)*u1[1]-um[0]-beta*lt[0])


def main():
    sys.set_int_max_str_digits(200000)
    log4=logarithm(Q(4));rows=[]
    for beta in (Q(1,4),Q(1,2),Q(3,4),Q(1)):
        b=entropy(beta)
        if beta<Q(1,2):assert b[1]<log4[0]
        if beta>Q(1,2):assert b[0]>log4[1]
        if beta==Q(1,2):assert b[0]<=log4[1] and b[1]>=log4[0]
        if beta==1:
            l6,l3=logarithm(Q(6)),logarithm(Q(3))
            assert b[0]<=l6[1]+l3[1]/2 and b[1]>=l6[0]+l3[0]/2
        finite=[]
        for n in (40,80,160):
            m=int(beta*n)
            W=sum(comb(n+2*m+1,m-j)*comb(n+j,j) for j in range(m+1))
            l=logarithm(Q(W))
            finite.append({'index':n,'length':m,'log_mass_per_index':outward_interval(l[0]/n,l[1]/n)})
        rows.append({'beta':str(beta),'entropy_interval':outward_interval(*b),'finite_checks':finite})
        print(beta,tuple(float(x) for x in b),flush=True)
    root=Path(__file__).resolve().parents[1]
    l2,l32=logarithm(Q(2)),logarithm(Q(3,2))
    joint=(7-l2[1]-12*l32[1],7-l2[0]-12*l32[0])
    assert joint[0]>Q(36,25)
    (root/'notes/saalschutz-entropy-threshold.json').write_text(json.dumps({
        'cases':rows,'selected_partial_quotient_rate_proved':False,
        'weight_seven_half_length_raw_cleared_first_term_rate':outward_interval(*joint),
        'scope':'Exact multiplier entropy enclosures; finite checks do not establish any CF-digit envelope.'},indent=2))


if __name__=='__main__':main()
