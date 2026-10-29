"""Choose moving integer points by exact continued fractions of each rational slope."""
from fractions import Fraction as Q
from pathlib import Path
import json,sys


def choose(A,h,theta):
    num,den=theta.numerator,theta.denominator
    p0,p1,q0,q1=0,1,1,0
    previous=(1,0); candidates=[]; steps=0
    while den:
        a,rem=divmod(num,den)
        p,q=a*p1+p0,a*q1+q0
        steps+=1
        if previous is not None:
            pp,qq=previous;V=max(q,qq)
            assert abs(p*qq-pp*q)==1 and V>0
            assert abs(theta*q-p)<=Q(1,V) and abs(theta*qq-pp)<=Q(1,V)
            envelope=A/(V*V)+h*V*V
            entry=(envelope,((pp,qq),(p,q)),V,steps)
            candidates.append(entry)
            if h*V**4>=A:break
        previous=p,q
        p0,p1,q0,q1=p1,p,q1,q
        num,den=den,rem
    assert candidates
    return min(candidates,key=lambda x:x[0])


def main():
    sys.set_int_max_str_digits(200000)
    root=Path(__file__).resolve().parents[1]
    data=json.loads((root/'notes/signed-prefix-metric.json').read_text())['cases']
    out=[]
    for row in data:
        A,B,C=map(Q,row['raw_binary_gram']);mu=Q(row['kernel_mass_majorant'])
        determinant=A*C-B*B;h=determinant/A;theta=B/A
        envelope,pairs,V,steps=choose(A,h,theta)
        values=[]
        for p,q in pairs:
            value=A*p*p-2*B*p*q+C*q*q
            assert value==A*(theta*q-p)**2+h*q*q and value<=envelope
            values.append(mu*value)
        bound=mu*envelope;optimal=Q(row['signed_prefix_cost_squared'])
        assert optimal<=max(values)<=bound
        assert bound<=Q(2073,1000)*optimal
        out.append({'weight':row['weight'],'index':row['index'],
                    'cutoff_multiple':row['cutoff_multiple'],'continued_fraction_steps':steps,
                    'integer_pairs':[[-p,q] for p,q in pairs],
                    'variable_point_upper_bound':str(bound),'upper_bound_over_gauss_optimum':str(bound/optimal),
                    'balance_fourth_power':str(Q(V**4)*h/A)})
    (root/'notes/variable-point-minimum.json').write_text(json.dumps({
        'cases':out,'uniform_balance_exponent_proved':False,
        'scope':'Exact moving integer pairs for forty finite metrics; no all-index decay inferred.'},indent=2))
    print(len(out),'unimodular moving-point pairs checked; worst bound/optimum',
          max(float(Q(x['upper_bound_over_gauss_optimum'])) for x in out))


if __name__=='__main__':main()
