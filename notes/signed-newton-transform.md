# Exact signed structure before arithmetic normalization

Let c_j=(-1)^j binom(n+2m+1,m-j)binom(n+j,j), 0<=j<=m.
The signed generating identity is

    sum_j c_j y^j=[z^m](1+z)^(n+2m+1)/(1+yz)^(n+1).

At y=1 this proves, at every n,m,

    sum_j c_j=binom(2m,m).                            (1)

Differentiating k times at y=1 and dividing by k! gives, for 0<=k<=m,

    sum_j c_j binom(j,k)
      =(-1)^k binom(n+k,k)binom(2m-k,m-k).             (2)

This is an exact signed identity, not an estimate based on alternating
signs. Algebraically it is generalized Chu-Vandermonde with negative
upper argument -(n+k+1). Lean verifies the unshifted and shifted
generalized binomial convolutions at all indices. Ring.choose_neg
identifies the negative binomial coefficients with the displayed signs.

## Exact transform for variable branch amplitudes

For any rational or real values f(0),...,f(m), Newton interpolation gives

    f(j)=sum_(k=0..j) binom(j,k) Delta^k f(0).

Substitute this finite identity and exchange the sums. Equation (2) yields

    sum_(j=0..m) c_j f(j)
      =sum_(k=0..m) (-1)^k binom(n+k,k)binom(2m-k,m-k) Delta^k f(0). (3)

Both sides are exact. In particular, a genuine signed analytic bound is

    abs(sum_j c_j f(j))
      <=sum_k binom(n+k,k)binom(2m-k,m-k) abs(Delta^k f(0)).

The differences, rather than the branch maxima, now carry the amplitude
information. No cancellation is asserted without evaluating these terms.

For a fixed-degree polynomial f with polynomially growing coefficients,
only finitely many differences occur. For fixed k and m/n->beta>0,
the moment factor has exponential rate beta*log4. At beta=1 the signed
mass itself has rate log4, exactly at the proposed threshold, not strictly
below it. Finite-order polynomial savings alone do not create a fixed
epsilon in that rate.

## Apply to the actual construction

For the actual Saalschutz branches

    R_j(t)=(n!)^s/(2m)! * (t-m-j)_(2m)/(t)_(n+1)^s,

each Laurent coordinate is a polynomial in j of degree at most 2m.
Coefficient extraction and the rational constant functional are linear,
so (3) applies to each coordinate. Their differences need not vanish at
a degree independent of n. Therefore the fixed-degree rate observation
does not bound the actual varying-degree amplitudes.

The script computes every pole jet of R_j directly, then forms the
finite Newton differences. At weights 7,9,11 it verifies the transformed
full coordinate vector against independent normalized logarithmic jets,
including the rational term and the cancellation of all even zeta rows.
Eight actual cases pass. It separately checks 1771 exact binomial-moment
identities through n=20.

This implements the signed-structure proposal for the actual forms.
The full kernel identity still reconstructs the original forms; no new
gcd saving or CF-digit bound follows merely from rewriting them. A
uniform primitive arithmetic bound on the transformed coefficients
still has not been proved at the needed rate. In particular the result
does not establish limsup log(a_n^*+1)/n<log4.

The other proposed frameworks require actual additional identities:
an oscillatory integral needs a proved phase/amplitude representation;
a resurgence argument needs its Borel transform and remainder control;
a Frobenius argument needs a specified integral module and valuations;
and a modular or differential-Galois argument needs the identified family
and a theorem implying the needed arithmetic rate. None is assumed here.
The exact signed transform is proved; the full irrationality theorem
remains unproved.

## Closed differences and exact positive decomposition

Repeated Pascal subtraction gives, for 0<=k<=2m,

    Delta^k R_0(t)=(-1)^k (n!)^s/(2m-k)!
                   * (t-m)_(2m-k)/(t)_(n+1)^s.       (4)

Indeed R_j has normalized numerator binom(t+m-j-1,2m), and each
backward difference reduces its lower binomial argument by one, shifts
the upper argument down by one, and changes its sign. Lean proves this
all-order generalized-binomial difference identity over the rationals.

For t>m define M_k=binom(n+k,k)binom(2m-k,m-k) and

    pi_k(t)=binom(m,k)(n+1)_k(t)_(m-k)/(t+n+1)_m.

Equations (3)-(4) imply M_k abs(Delta^k R_0(t))=pi_k(t)T(t).
Rising-factorial Vandermonde gives sum_k pi_k(t)=1, and every pi_k
is nonnegative. Therefore the analytic triangle bound is exactly

    sum_k M_k abs(Delta^k R_0(t))=T(t).              (5)

There is no branch-mass loss in (5). The same equality holds after
summing over integer t>m. This closes the raw signed analytic estimate.
It does not transfer positivity to the Laurent expansions at t=-h.
The script checks 693 exact rational convex identities in addition to
1771 moments and eight full coordinate transformations.

## All-index coefficient envelope after the signed combination

Write T(t)=sum_(h=0..n)sum_(q=1..s) A_(q,h)/(t+h)^q, with n>=1,
0<=m<=n and s>=3. Put rho=1/(2(n+1)) and

    B_h=binom(n,h)^s binom(h+m,m)binom(n-h+m,m).

On |t+h|=rho, the analytic function (t+h)^s T(t) has absolute value
at most e^(s+1) B_h. For the numerator, the logarithmic increase from
its value at t=-h is at most 2m rho<=1. For the denominator use
-log(1-u)<=2u for 0<=u<=1/2: its increase is at most
2s rho (H_h+H_(n-h))<=s. Cauchy's coefficient estimate now gives

    abs(A_(q,h))<=e^(s+1) B_h [2(n+1)]^(s-q).       (6)

This is a proof for every index, not an extrapolation. Symmetry and
the ratio

    B_(h+1)/B_h=((n-h)/(h+1))^s
                 * (h+m+1)(n-h)/((h+1)(n-h+m))

show that B_h is maximal at h=floor(n/2). If U_n is the maximum of
the absolute zeta-row coefficients and the rational coefficient after
summing the poles, H_(h,q)<=n yields

    U_n<=s n(n+1)e^(s+1)[2(n+1)]^(s-1) B_floor(n/2). (7)

For fixed s and m/n->beta in [0,1], Stirling's formula proves

    limsup log(U_n)/n
      <=s log2+(1+2beta)log(1+2beta)-2beta log(2beta), (8)

using 0 log0=0. At beta=1 the bound is (s-2)log2+3log3; at s=7
it is approximately 6.761573. This is an explicit coefficient envelope,
not an estimate of the primitive gcd or the lattice minimum. Clearing
denominators or imposing cancellation conditions still has its own
arithmetic cost. In particular (8) is not the negative scalar rate.

The script also evaluates the exact rational product bound on each
Cauchy circle, before the exponential simplification, and checks every
coordinate against it in the eight actual cases. The Cauchy and
Stirling arguments in this section are paper proofs, not claims of
full Lean formalization.
