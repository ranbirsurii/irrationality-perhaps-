# Exact multiplier entropy and the five proposed routes

This calculation proves an exact all-index asymptotic for the explicit
Pfaff-Saalschutz multiplier mass. It does not identify that mass with
the selected continued-fraction digit a_n^*.

Let m_n/n->beta in (0,1], and

    W_(n,m)=sum_(j=0..m) binom(n+2m+1,m-j)binom(n+j,j).

## Exact asymptotic by real Laplace maximization

Put x=j/n. Uniform factorial bounds, including endpoints with 0 log 0=0,
give log|c_j|=n E_beta(x)+O(log(n+1)), with beta=m/n and

    E_beta(x)=(1+2beta)log(1+2beta)
      -(beta-x)log(beta-x)-(1+beta+x)log(1+beta+x)
      +(1+x)log(1+x)-x log x.

On 0<x<beta,

    E'_beta(x)=log((beta-x)(1+x)/(x(1+beta+x))),
    E''_beta(x)=-1/(beta-x)-1/(1+beta+x)+1/(1+x)-1/x<0.

The unique maximum is x_beta=(sqrt(1+2beta)-1)/2. The largest
summand is <=W<=(m+1) times the largest summand. Selecting an integer
j nearest n*x_beta proves the matching lower rate by the same uniform
factorial bounds. Thus, for the whole sequence m_n/n->beta,

    lim log W_(n,m_n)/n=c(beta)=E_beta(x_beta).

Equivalently put t_beta=beta/(1+beta+sqrt(1+2beta)). Algebra gives

    c(beta)=(1+2beta)log(1+t_beta)-log(1-t_beta)-beta log(t_beta).

This agrees with the large-powers saddle framework in
[Flajolet-Sedgewick, Analytic Combinatorics, Chapter VIII](https://ac.cs.princeton.edu/home/AC.pdf),
but the exponential-rate proof here uses only uniform factorial bounds
and a maximum term. No contour deformation or unproved saddle prefactor
is needed.

## Sharp threshold

The saddle equation makes the derivative through t_beta vanish, so

    c'(beta)=2log(1+t_beta)-log(t_beta)>0.

At beta=1/2, t_beta=3-2sqrt(2). The exact identity

    (1+t)^4-16t(1-t)^2=(t^2-6t+1)^2

proves c(1/2)=log4. At beta=1, direct substitution gives
c(1)=log(6sqrt(3)). Consequently

    c(beta)<log4 iff beta<1/2.

For the original fixed-weight blocks m=n-r with s=2r+1 fixed, beta->1,
so the exact mass rate is log(6sqrt(3)), above log4. The old envelope's
exponential base is sharp in that regime, rather than a removable loss
from triangle inequalities.

An independent numerator-length offset h_n may be varied in the
previously constructed alternative family. Its effect on analytic decay,
coefficient extraction, denominators and the inverse map must be retained.
The weight r itself is fixed when the target is a prescribed zeta value.
No bound for a_n^* is inferred even when beta<1/2: W and a_n^* are
different quantities, and the required transfer inequality is not proved.

## Scope of the other four routes

1. The entropy route above is completed for W, with its precise threshold.
2. The [Gauss-Kuzmin-Wirsing operator](https://www.impan.pl/en/publishing-house/journals-and-series/acta-arithmetica/all/24/5/100120/on-the-theorem-of-gauss-kusmin-levy-and-a-frobenius-type-theorem-for-function-spaces)
   controls metrical/distributional quantities under its hypotheses. A
   spectral gap is not an all-index digit bound for the prescribed moving
   rational slopes. No qualifying uniform pointwise estimate is identified.
3. Interval arithmetic gives finite certificates. An independent analytic
   or inductive tail bound is still necessary; increasing a finite cutoff
   does not prove that tail bound. No such closing tail certificate is found.
4. Cauchy-Hadamard would turn an established radius >1/4 for the generating
   function of a_n^*+1 into the required rate. No holonomic recurrence for
   this CF-selected sequence is proved. A recurrence for the underlying
   rational coefficient rows does not automatically survive CF selection.
5. Parameter optimization is quantified exactly by c(beta). It improves
   multiplier mass for smaller beta but does not certify the full cost or
   the local CF-digit rate for the isolated target.

The analytic cost can also be checked at the tempting half-length
threshold. The exact first positive kernel term is

    T_(s,n,m)(m+1)=(n!)^s*(m!)^(s-1)*(n+2m+1)!/((n+m+1)!)^(s+1).

For m/n->beta its logarithmic rate is

    (s-1)beta log beta+(1+2beta)log(1+2beta)
       -(s+1)(1+beta)log(1+beta).

At s=7, beta=1/2, multiplying by d_n^7 gives rate
7-log(2)-12log(3/2)>1.44. The positive raw sum is at least this first
term. Thus shortening to this threshold loses the raw decay versus
LCM budget; the smaller multiplier mass does not close that budget.
This statement concerns the raw positive sum, not a proof excluding
signed cancellation or further primitive gcd savings.

## Verification

Four Lean statements verify the stationary polynomial, strict concavity,
the half-radius identity, and the exact logarithmic value at that saddle.
The uniform factorial asymptotic and transfer discussion are paper proofs,
not an assertion that the whole saddle theorem has been formalized.
The script encloses c(beta) rationally at beta=1/4,1/2,3/4,1 and checks
the corresponding masses at n=40,80,160. It labels the CF-digit growth
bound unproved. The required strict rate and all-odd theorem remain open
in this project; none of the five methods has closed them here.
