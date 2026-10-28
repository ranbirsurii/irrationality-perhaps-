# Higher-weight construction and relative arithmetic cost

The target is unconditional irrationality of every odd zeta value at least
seven. The present result is a conditional criterion, not that theorem.
This record distinguishes the estimates actually derived from those still
required for the specified Padé family.

Subsequent update: `augmented-rank-discrete-residue-proof.md` now proves
full augmented rank and lower-row rank on paper for every actual
consecutive-block profile at even n>=2r. Consequently a pair of primitive
signed kernel forms cannot both vanish. This supplies the alternative to
positive-weight nonvanishing; the normalized arithmetic cost is still
required. The older route-specific discussion below is retained.

## A direct higher-weight analytic comparison

For the normalized kernels in the manuscript, put

\[
 Q_n(k)=n!/[k(k+1)\cdots(k+n)].
\]

Then T_(s,n,m)(k)=Q_n(k)^(s-5) T_(5,n,m)(k). The central binomial
inequality gives Q_n(n+1)<=4^(-n). For n>=2r, 0<=j<=r and k>=n-j+1,
the successive quotient Q_n(k)/Q_n(k+1)=(k+n+1)/k is at most three
for each necessary backward step. Hence Q_n(k)<=3^j*4^(-n).
The exact fixed-shift factorial identity gives

\[
 A_{s,n,n-j}\le 3^{j(s-5)}(3^6/4)^j A_{5,n,n}
                            4^{-(s-5)n}.
\]

Together with the earlier analytic base estimate this proves the stated
raw higher-weight bound, on paper, for every eligible index. It is not a
claim about the primitive integer forms. Lean separately proves

\[
 \log140+(s-5)\log4>s+1/3\quad(s\ge7).
\]

The permitted arithmetic cost is actually larger than subexponential:
any upper exponential rate strictly below
log(140)+(s-5)log(4)-s would suffice. At weight seven this budget is
between 0.7142311 and 0.7142312. Relaxing the sufficient condition does
not establish an estimate for the actual positive cancellation vectors.

## An exact local reformulation

For a primitive lower row ell and an integral Bezout column u with ell*u=1,
Pi=I-u*ell maps the full integer lattice onto its kernel. The Lean theorem
`dvd_projectedRowsContent_iff` proves, for every integer c, that c divides
the entry gcd of F*Pi precisely when it divides F(v) for every integer
kernel vector v. This handles the division by the lower-row gcd before
testing divisibility. It does not assert that any specified p^e divides
these entries. Such a congruence remains to be proved from the actual jets.

## Checking a contemporary arithmetic-factor method

Li Lai, *A note on the number of irrational odd zeta values, II*,
arXiv:2501.05321v2, Lemma 3.3, derives an explicit prime-product saving
from a floor-function minimum for its factorial family:
https://arxiv.org/pdf/2501.05321

The single unshifted denominator block has the corresponding floor
expression

\[
 \omega(x)=\min_{0\le y<1}
    (\lfloor x\rfloor-\lfloor y\rfloor-\lfloor x-y\rfloor)=0.
\]

Indeed floor(y)=0, floor(x-y)<=floor(x), and y=0 gives equality.
Consequently this particular uniform binomial-factor minimum contributes
no positive prime-product saving in a single unshifted block. This is not
an assertion that the actual sums or determinant minors have no additional
divisibility: their cancellations may provide extra factors. Those factors
must be established for these coefficients; the external theorem concerns
a different rational function and is not an identification with Gamma_n.

## Exact separation of row balance and positive integral cost

For t>=2 let C=(t,-(t-1),t), Y=(1,0,0), Z=(0,0,1).
The row is primitive, its rank is one, its kernel has rank two, and the
positive-to-negative row-sum ratio is at most four. Its kernel contains
(1,0,-1), so the content of the target and constant evaluations is one.

Every nonzero nonnegative integer kernel vector (a,b,c) satisfies
t(a+c)=(t-1)b. Thus k=b-a-c is a positive integer,
a+c=(t-1)k, b=tk, and a+b+c=(2t-1)k. The least mass is exactly
2t-1, attained at (t-1,t,0). With t=2^n this cost grows exponentially
despite bounded row balance and unit image content. These universal
inequalities are proved in `PositiveCancellationCost.lean`.

This is not the zeta family and does not disprove its desired estimate.
It proves that removing the estimate as a supposed automatic consequence
of these structural properties would be an invalid inference.

## Remaining construction-specific tasks

The signed cofactor alternative has an additional exact restriction.
For any integral kernel basis a,b, put U=Y(a)b-Y(b)a and
delta=Y(a)Z(b)-Y(b)Z(a). If the augmented determinant is nonzero, then
delta!=0, Y(U)=0, C(U)=0, and Z(U)=delta. Moreover Gamma^2 divides delta.
The cleared period identity therefore gives

\[
 \Gamma_n^2\le|\delta|
  \le d_n^s\sqrt{r+1}\,\mathcal M_n S_n,
 \qquad\mathcal M_n=\max(\|U_Y\|_2,\|U_Z\|_2).
\]

Thus the cofactor ratio Gamma_n^2/mathcal_M_n has upper exponential
rate at most s-a_s under the explicit analytic bound. At weight five,
the coarse upper rate is 5-log(140)<0.058358, so a lower bound with
exponent 0.06 is impossible along an unbounded sequence of full augmented
rank. With the sharp saddle estimate the upper rate is less than
0.029207, excluding the proposed 0.03 cofactor lower exponent.
This does not exclude the weaker Gamma_n/lambda_(2,n) estimate: the
cofactor norm may be much larger than Gamma_n*lambda_(2,n).

The signed companion formalizes the integer-divisor argument and the
universal signed norm inequality. Independently, the actual normalized
weight-seven coefficients at n=6,8, computed by two algorithms, give
exact target-free cofactor combinations with nonzero integral constant
delta/Gamma^2. They check the algebra on the construction itself, without
an inference about large indices. The same tests confirm positive
lower-period cancellation vectors at those indices; they do not yield
the missing asymptotic cost estimate.

At every fixed higher odd weight, construct positive integral weights
annihilating every lower odd-zeta row, and bound their mass divided by the
actual image content within the analytic budget above. The rank condition
alone gives an integer kernel vector, but does not give nonnegativity or
the needed mass bound. No proof of these two claims was obtained here.
The supplied Smith-content note itself states them as hypotheses in its
Corollary 3 and in its final paragraph. The weight-five joint content and
basis-length estimate is also not proved.
