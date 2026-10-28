# An analytic formulation without the explicit lcm factor

The existing bound has an exact reformulation that removes the explicit
denominator-clearing factor. This is an identity for the same quantity,
not an additional assumption or a change of construction. It does not
by itself prove that the quantity tends to zero.

For every r>=3, odd s=2r+1, and even n>=2r, let A be the original rational
coefficient matrix before clearing denominators, D=d_n^s, and M=DA.
Let E embed the target-and-constant coefficient pair, and let H be the
weighted Newton profile map. Using the moment matrix G already defined,
put

    F_raw=H A^(-1) E,   S_raw=F_raw^T G F_raw.

The cleared construction has F=H M^(-1)E=F_raw/D, hence S=S_raw/D^2.
Positive scalar multiplication leaves the exact binary Gauss reduction
choices unchanged: comparisons of diagonal entries and the quotient
2B/A are invariant. In particular, if the reduced second coefficient
of S_raw is v_raw, then v_raw=D^2 nu. Therefore exactly

    R_(s,n)=d_n^(2s) mu nu = mu v_raw.

For every real coefficient pair y the earlier Cauchy--Schwarz argument
now reads

    |a*zeta(s)+b|^2 <= mu y^T S_raw y.

For the two reduced primitive basis pairs it gives |L_i|^2<=mu v_raw.
The same unimodular basis serves both scaled metrics. In reduced real
coordinates (h,k), the all-form bound is

    |L(U(h,k))|^2 <= (3/2) mu v_raw (h^2+k^2).

Thus prime-power jumps in D need not be estimated separately in this
formulation. The earlier ratio decomposition involving D is still an
identity, but it is unnecessary to bound its factors independently.
This corrects the impression that a separate prime-jump estimate is
intrinsically required. Rational coefficients and the integer choice of
primitive pairs are still present in S_raw and its reduction; this
identity is not a theorem that their effect is negligible.

## Exact index transition of the common kernel

For m=n-r, t>m, define

    K_(s,n,m)(t)=
      (((n+1)(n+2))^s / ((m+1)(m+2))^2)
      * [t(t+1)]^(s+1)
      * product_(j=1..6)(t+n+m+j)
      / product_(j=1..4)(t+n+j)^(s+1).

Then the original normalized kernel satisfies

    T_(s,n+2,m+2)(t+2)=K_(s,n,m)(t) T_(s,n,m)(t).

Proof: the negative-root numerator product changes by t(t+1).
The positive-shift numerator product changes by its last six factors
divided by its first four factors. The denominator product changes
by product_(j=1..4)(t+n+j)/[t(t+1)]. Finally the factorial prefactor
changes by ((n+1)(n+2))^s/((m+1)(m+2))^2. Multiplication gives the
formula. It remains valid when the displayed factors overlap, since
the common factors cancel exactly. All factors are positive on t>m.

The shift k->k+2 aligns the complete summation ranges: m+1 maps to
(m+2)+1. Thus no initial summands are lost when this transition is used
in a moment comparison. The profile coordinate w and the inverse
coefficient matrix also change with n; the kernel multiplier alone
does not compare the reduced metrics.

## Uniform analytic contraction of the kernel

For every r>=3, s=2r+1, n>=4r, and real t>=m+1, the multiplier obeys

    0<K_(s,n,m)(t) <= (1/100) 16^(-(s-7)).

Here n need not be even for the product inequality. To prove it, put
x=t/n>0. The explicit multiplier above is at most C_(s,n) f_s(x), where

    C_(s,n)=(1+2/n)^(3s+1) (1+3/n)^6 / (1-r/n)^4,
    f_s(x)=x^(2s+2)(x+2)^6/(x+1)^(4s+4).

Indeed t>=n-r+1>=n/2 gives t(t+1)<=t^2(1+2/n).
Each of the six upper numerator factors is at most
(t+2n)(1+3/n), and every lower denominator factor is at least t+n.
The factorial prefactor is at most
n^(2s-4)(1+2/n)^(2s)/(1-r/n)^4. The powers of n cancel.

Next x^2/(x+1)^4<=1/16, so f_s<=16^(-(s-7))f_7.
Since x+2<=2(x+1),

    f_7(x)<=64*x^16/(x+1)^26 <= q0,
    q0=64*8^16*5^10/13^26.

The last maximum is at x=8/5: the logarithmic derivative of
x^16/(x+1)^26 has the sign of 16-10x. Finally log(1+z)<=z gives

    C_(s,n) <= (4/3)^4 exp((12r+26)/n)
             <= (4/3)^4 exp(31/6) < (4/3)^4*3^6=2304.

The last strict inequality uses e<3 and 31/6<6. Exact integers verify
2304*q0<1/100. This proves the asserted uniform contraction.

Consequently the actual positive kernel mass
M_(s,n)=sum_(k>n-r) T_(s,n,n-r)(k) satisfies

    M_(s,n+2) <= (1/100)16^(-(s-7)) M_(s,n),  n>=4r.

This follows by the exact alignment of the summation ranges and
termwise comparison of convergent positive series. It is an all-index,
all-weight analytic theorem, not an extrapolation of the finite checks.
It concerns the true kernel mass M, not automatically the certified
upper envelope mu used in the stored moment matrices. More importantly,
the profile map and its reduced metric vary with n. This kernel theorem
does not establish contraction of mu*v_raw. That product remains the
same unproved final target.

The remaining limit can now be attacked directly as

    mu_(s,n) v_raw_(s,n) -> 0,

or by proving a contraction of this product. This is precisely the
previous limit, with no new independent condition. A proof comparing
the reduced metrics across indices has not been obtained here.

## Verification

`analytic_kernel_transition.py` checks twelve matrix-scale identities
across weights 7,9,11,13,17,21 at n=2r and 4r, and 48 exact rational
kernel transitions. It verifies identical unimodular Gauss witnesses
under scaling and agreement of the complete bounds. The script stores
fractions only. These are finite checks of the displayed algebraic
identities, whose proofs above apply at all eligible indices. No
limiting assertion is inferred. The full family identification in this
note has not been formalized in Lean; the previously checked common
factor lemma verifies its scalar cost identity.
