# Augmented rank by discrete residues and a degree count

Fix r>=1, s=2r+1, an even integer n>=2r, and the r+1 blocks
m=n-r,n-r+1,...,n. For the actual normalized kernels

  T_m(t) = (n!)^s/(m!)^2 * product_{v=1}^m (t-v)(t+n+v)
             / product_{j=0}^n (t+j)^s,

let v_m be the rational coefficient column in the order
zeta(3),zeta(5),...,zeta(s),constant. These columns are defined by the
partial-fraction expansion and the finite harmonic boundary formula.

**Theorem.** The square matrix with columns v_(n-r),...,v_n is invertible
over Q for every specified r,n. Consequently its integer-cleared augmented
matrix has full rank r+1, and its lower-period submatrix has row rank r-1.
No irrationality assertion, asymptotic estimate, or finite-index
extrapolation enters this result.

## Ten candidate methods

| Method | Assessment for this rank problem |
| --- | --- |
| 1. Discrete residues and polynomial zero count | Chosen. The explicit antidifference and the existing common zeros give a complete proof below. |
| 2. General Hermite-Pade normality | Would need identification of this exact rational-function and boundary map; method 1 proves the needed normality directly. |
| 3. Casoratian transport in the block length | A recurrence transports a nonzero determinant but still needs a uniform nonzero initial determinant; method 1 supplies nonvanishing without that initialization. |
| 4. Total positivity of a moment matrix | Would require a common positive moment representation for the residue and rational-boundary rows; raw positivity of each sum alone is insufficient. |
| 5. Gram positivity and min-max | Proves rank once independence or a positive lower determinant is known; it does not itself identify that determinant for these columns. |
| 6. Uniform saddle asymptotics of the determinant | Requires control of leading cancellation among coefficient columns; unnecessary for this finite-degree proof. |
| 7. Modular nonvanishing at an auxiliary prime | An exact nonzero reduction would suffice, but a uniform choice of prime and residue formula is an extra arithmetic task avoided here. |
| 8. Smith normal form | Detects rank of each evaluated matrix; an all-index invariant-factor formula would still be needed without method 1. |
| 9. Differential-Galois or motivic rank | Requires an explicit identification of this finite coefficient map and its rational boundary component; the elementary residue map already describes both. |
| 10. Rational summation in an Ore algebra | Equivalent in this one-pole-orbit situation to the explicit discrete-residue calculation below; the direct construction avoids a black-box summation algorithm. |

The general relation between rational summability and discrete residues
is discussed by Arreche and Sitaula in
[Computing discrete residues of rational functions](https://arxiv.org/abs/2402.07328)
and their [2025 continuation](https://arxiv.org/abs/2503.15636).
The argument below constructs the antidifference explicitly, so does not
invoke either paper as an unproved identification of this family.

## 1. A hypothetical zero column combination

Take rational weights w_m with sum_m w_m v_m=0 and put
F(t)=sum_m w_m T_m(t). Its denominator is

  R(t)=product_{j=0}^n(t+j)^s.

Its numerator H has degree at most 2n. It vanishes at t=1,...,m0,
where m0=n-r, because every block has those numerator factors.
The reflection is F(-n-t)=-F(t), because n is even and s is odd.
F is strictly proper and has the unique partial-fraction expansion

  F(t)=sum_{q=1}^s sum_{j=0}^n c_(j,q)/(t+j)^q.

Reflection gives c_(n-j,q)=(-1)^(q+1)c_(j,q).
Thus sum_j c_(j,q)=0 for every even q. The assumed zero period
coordinates give this equality for odd q=3,5,...,s. For q=1 it follows
from F(t)=O(t^(-2)) at infinity: the coefficient of t^(-1) is zero.
Therefore

  sum_{j=0}^n c_(j,q)=0 for every 1<=q<=s.

The assumed zero constant coordinate is

  Z(F) = -sum_{q=1}^s sum_{j=0}^n c_(j,q) H_j^(q) = 0,
  H_j^(q)=sum_{k=1}^j k^(-q).

These are identities of rational numbers, with no independence assumption
on the real zeta values.

## 2. An explicit rational antidifference and its boundary

For 0<=h<=n-1 set

  b_(h,q)=-sum_{j=0}^h c_(j,q),
  G(t)=sum_{q=1}^s sum_{h=0}^{n-1} b_(h,q)/(t+h)^q.

Coefficient comparison at each pole gives exactly

  G(t+1)-G(t)=F(t).

Indeed the coefficient at j=0 is -b_(0,q)=c_(0,q), at
1<=j<=n-1 it is b_(j-1,q)-b_(j,q)=c_(j,q), and at j=n it is
b_(n-1,q)=c_(n,q), using the zero total residue.

Finite summation, again using the zero total residue, gives

  G(1)=-sum_{q,j} c_(j,q)(H_n^(q)-H_j^(q))
      =sum_{q,j} c_(j,q)H_j^(q)=-Z(F)=0.

Reflection of the prefix sums gives

  b_(n-1-h,q)=(-1)^q b_(h,q),
  G(1-n-t)=G(t).

This symmetry follows directly by replacing h with n-1-h in the finite
partial-fraction sum. No assertion about periodic rational functions is
needed.

## 3. The exact polynomial degree drop

Let Q(t)=product_{h=0}^{n-1}(t+h). Combining the displayed fractions,
write G(t)=P(t)/Q(t)^s. Because every term of G is strictly proper,
deg(P)<=sn-1 unless P=0. The difference equation is the polynomial identity

  H(t)=t^s P(t+1)-(t+n)^s P(t).

Suppose P!=0, let d=deg(P), and let a!=0 be its leading coefficient.
The coefficients of t^(d+s) cancel. The coefficient of t^(d+s-1) is

  (d-sn)*a.

For d=0 the same formula follows directly from the two powers.
For d>=1 the next coefficient of P occurs in both terms and cancels;
the shifted leading monomial contributes d*a in the first term, and
(t+n)^s contributes sn*a in the second. Because d<=sn-1, this
coefficient is nonzero. Hence

  deg(H)=d+s-1 <= 2n,
  d <= 2n-s+1 = 2(n-r)=2m0.

This is an exact degree calculation, not an asymptotic estimate.

## 4. Too many roots

For k=1,...,m0, F(k)=0 and both G(k),G(k+1) are regular. Starting from
G(1)=0, the difference identity implies

  G(k)=0 for k=1,...,m0+1.

Reflection supplies the additional roots

  G(-n),G(-n-1),...,G(-n-m0)=0.

All 2m0+2 points are distinct and avoid the poles 0,-1,...,1-n of G.
Consequently P vanishes at all of them. A nonzero polynomial of degree
at most 2m0 cannot have 2m0+2 distinct roots. Thus P=0, G=0, and F=0.

Finally the normalized numerator polynomials of T_(n-r),...,T_n have
distinct degrees 2(n-r),2(n-r+1),...,2n and nonzero leading coefficients.
They are linearly independent over Q: the largest degree with a nonzero
weight could not cancel. Therefore every w_m is zero. The square
coefficient matrix is injective and hence invertible. Reversing the
column order or clearing by d_n^s preserves its rank.

## Consequences and formalization scope

The result removes the lower-row and augmented-rank hypotheses for this
specific consecutive-block profile, at every even n>=2r. Thus the
two primitive signed forms in manuscript Proposition 8.1 cannot both
vanish once an integral kernel basis is chosen. The remaining cost
estimate is still required to deduce irrationality.

This note is a complete paper proof of augmented rank. A separate Lean
verification record states precisely which algebraic ingredients have
been formalized. A proof of the root-count implication alone is not
represented as a full Lean formalization of the family identification.
