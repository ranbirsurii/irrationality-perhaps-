# An all-index coefficient envelope and a higher-weight prime divisor

Fix an odd weight s=2r+1>=5, even n>=2r, and 0<=m<=n. These
statements concern the actual factorial-normalized rational kernel in
the manuscript. They are paper proofs. The determinant and Cramer-vector
envelope used below is independently formalized in
`OddZeta/CramerKernelEnvelope.lean`.

## A uniform coefficient envelope

Write c_(j,k) for the Laurent coefficients at -j. The leading one has
absolute value

  abs(c_(j,s))=binom(n,j)^s binom(j+m,m) binom(n-j+m,m)
              <=2^((s+3)n).

After dividing the local expansion by this nonzero leading coefficient,
there are 2m factors 1+/-x/a in the numerator and sn inverse linear
factors, with every abs(a)>=1. Taking absolute coefficients majorizes
their product by

  (1+x)^(2m) (1-x)^(-sn) <=_coeff (1-x)^(-(s+2)n).

For degrees u<=s-1 its coefficient is at most
(((s+2)n+s))^(s-1). Therefore, for every period coefficient a_k,

  abs(a_k(n,m))<=E_s(n),
  E_s(n)=(n+1)(((s+2)n+s))^(s-1) 2^((s+3)n).

This is an inequality at every eligible index, without an asymptotic
expansion or a finite-index extrapolation.

## Translation traces at every odd weight

For odd 3<=k<=s-2 define the integer prime product

  G_(s,k,n)=product of p over n<p<=((s-2)/(k-1))n.

Then for every 0<=m<=n,

  G_(s,k,n) divides d_n^(s-k) a_k(n,m).

Here the quantity on the right is an integer by the weighted Taylor
denominator theorem. The proof generalizes the already established
weight-five interval n<p<=3n/2.

Take a prime p in the displayed interval. Since n>=s-1, p>=s. All
factorial and Laurent denominators are p-integral. Over F_p put
F(t)=t^p-t and reduce the rational function T modulo p. Its denominator
divides F^s, so P=F^s*Tbar is a polynomial of degree at most

  sp+2m-s(n+1).

For any polynomial P, translation trace Tr(P)=sum_(a in F_p)P(t+a)
has degree at most deg(P)-(p-1), or is zero. Expand monomials: the
coefficients using sum_a a^h vanish for 0<=h<p-1, including h=0.
Also F(t+a)=F(t), and differentiation of F'/F=-1/F gives

  sum_(a in F_p) (t-a)^(-ell)=(-1)^ell F(t)^(-ell), 1<=ell<=s.

The differentiating factorials are units since ell-1<p. It follows
from the reduced partial fractions that

  Tr(P)=sum_(ell=1..s) (-1)^ell abar_ell F^(s-ell).

The trace degree is at most

  (s-1)p+2m-sn-s+1
  <=(s-1)p-(s-2)n-s+1
  <=(s-k)p-s+1 < (s-k)p.

The powers of F have distinct degrees. Comparing the largest nonzero
power and proceeding downwards forces abar_ell=0 for all ell<=k.
In particular a_k is divisible by p locally. As p>n is coprime to d_n,
the cleared integer coefficient is divisible by p. Distinct primes give
the asserted product divisor. This proof covers all block lengths at
once; it is not a claim about higher-order minors after gcd division.

## The resulting uniform cost estimate

Divide lower row k by G_(s,k,n), after clearing it naturally by d_n^(s-k).
This preserves the rational and integral kernels: all divisors are
nonzero. A nonzero (r-1)-column minor exists by the augmented-rank proof.
Cramer's construction with each of the two free columns produces
independent integer kernel vectors, each of mass at most

  r! d_n^(r(r-1)) E_s(n)^(r-1)
      / product_(q=1..r-1) G_(s,2q+1,n).

The determinant expansion bounds a minor by (r-1)! times the product
of its row bounds, and there are at most r nonzero coordinates. Full
augmented rank makes their two coefficient images independent. Their
individual integer gcds are at least one. Thus this is also an upper
bound for the optimal primitive-pair Euclidean cost W_n.

The prime number theorem gives, at fixed s,k,

  log(G_(s,k,n))/n -> (s-2)/(k-1)-1.

Consequently a proved upper exponential rate for W_n is

  B'_s=r(r-1)+(s+3)(r-1)log(2)
       -((s-2)/2 H_(r-1)-(r-1)).

This is a strict arithmetic improvement over the elementary determinant
envelope. At weight seven the improvement is exactly 7/4 in the exponent.
It still does not give the required upper rate below a_s-s. For example
the bound at weight seven exceeds 18, while a_7-7 is between 0.7142311
and 0.7142312. More generally the subtracted prime contribution is less
than r(r-1), so B'_s>(s+3)(r-1)log(2)>s-5>a_s-s for r>=3.

An upper bound that is too large does not imply a lower bound for W_n.
It neither disproves the desired estimate nor completes irrationality.
The selected sharper route remains the exact reduced binary form,
whose unproved family estimate is recorded in the manuscript.
