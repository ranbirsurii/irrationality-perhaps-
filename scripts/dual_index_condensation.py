"""Rational parallel-sum condensation of complete moment bounds."""
from fractions import Fraction as Q
from pathlib import Path
import json
import sys

from moment_metric_reduction import construct
from check_dual_cost_reduction import reduce_binary_form
from zeta_enclosure import euler_maclaurin_zeta_interval


def mul(A,B):
    return [[sum((A[i][k]*B[k][j] for k in range(2)),Q(0)) for j in range(2)] for i in range(2)]


def transpose(A):return [list(row) for row in zip(*A)]


def inv(A):
    d=A[0][0]*A[1][1]-A[0][1]*A[1][0]
    assert d!=0
    return [[A[1][1]/d,-A[0][1]/d],[-A[1][0]/d,A[0][0]/d]]


def quad(A,y):return sum((y[i]*A[i][j]*y[j] for i in range(2) for j in range(2)),Q(0))


def metric(row):
    a,b,c=map(Q,row['reduced_gram'])
    scale=Q(row['full_moment_bound'])/c
    U=[[Q(row['forms'][j]['primitive_pair'][i]) for j in range(2)] for i in range(2)]
    Ui=inv(U)
    return mul(mul(transpose(Ui),[[scale*a,scale*b],[scale*b,scale*c]]),Ui)


def main():
    sys.set_int_max_str_digits(200000)
    records=[]
    for r,n in ((3,12),(3,20),(3,40),(3,80),(3,160),(4,16),(4,40),(5,20)):
        first,second=construct(r,n),construct(r,n+2)
        A,B=metric(first),metric(second)
        Ai,Bi=inv(A),inv(B)
        old=min(Q(first['full_moment_bound']),Q(second['full_moment_bound']))
        candidates=[]
        for t in (Q(0),Q(1,100),Q(1,10),Q(1,2),Q(9,10),Q(99,100),Q(1)):
            H=inv([[t*Ai[i][j]+(1-t)*Bi[i][j] for j in range(2)] for i in range(2)])
            reduced,U,steps=reduce_binary_form(H[0][0],H[0][1],H[1][1])
            candidates.append((reduced[2],t,H,U,steps))
        new,t,H,U,steps=min(candidates,key=lambda row:row[0])
        assert new<=old
        lo,hi=euler_maclaurin_zeta_interval(2*r+1,max(96,2*(n+2)))
        for col in range(2):
            y=[Q(U[i][col]) for i in range(2)]
            Jy=[sum(H[i][j]*y[j] for j in range(2)) for i in range(2)]
            a=[t*sum(Ai[i][j]*Jy[j] for j in range(2)) for i in range(2)]
            b=[(1-t)*sum(Bi[i][j]*Jy[j] for j in range(2)) for i in range(2)]
            assert [a[i]+b[i] for i in range(2)]==y
            if 0<t<1:
                assert quad(A,a)/t+quad(B,b)/(1-t)==quad(H,y)
            actual=max(abs(y[0]*lo+y[1]),abs(y[0]*hi+y[1]))
            assert actual*actual<=quad(H,y)<=new
        records.append({'weight':2*r+1,'first_index':n,'second_index':n+2,
                        'selected_mixing_parameter':str(t),
                        'tested_mixing_parameters':list(map(str,(Q(0),Q(1,100),Q(1,10),Q(1,2),Q(9,10),Q(99,100),Q(1)))),
                        'condensed_second_bound':str(new),
                        'best_single_second_bound':str(old),
                        'single_over_condensed_ratio':str(old/new),
                        'condensation_improves_bound':new<old,'gauss_steps':steps})
        print(2*r+1,n,'improves',new<old,'factor',float(old/new),flush=True)
    root=Path(__file__).resolve().parents[1]
    (root/'notes/dual-index-condensation.json').write_text(json.dumps({
        'cases':records,'uniform_decay_proved':False},indent=2))


if __name__=='__main__':main()
