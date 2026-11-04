# November continuation: reconcile the chats and sharpen a local estimate

The following chats were read on November 4, 2026:

- Prove Fourier Hodge Theorem
- Continue Fourier analysis
- Odd Zeta Bounds Analysis
- Proving Odd Zeta Irrationality
- Extend Q By Odd Zeta Values

Their latest conclusions retain an unproved deterministic arithmetic estimate.
They contain two distinct routes: Fourier estimates for linear Padé forms,
and positive powered Hankel polynomials in a single target value. Their
normalizations and index scales must not be interchanged.

## A sharper polynomial-moment prime cutoff

For the powered Hankel route, put L=2e+2 and

    mu_s(t^e) = (-1)^e B_L product_(j=1..s-2)(L+j)/(s-1)!.

Let s>=3, e>=0, and let p>s be prime. The von Staudt-Clausen theorem says
that B_L has p-valuation -1 if p-1 divides L, and is p-integral otherwise.
The factorial (s-1)! is a p-unit.

If L=k(p-1), the numerator factor L+j is divisible by p exactly when
j=k modulo p. Since 1<=j<=s-2<p, we obtain the exact support criterion:

    mu_s(t^e) is not p-integral
    iff (p-1)|L and k mod p is outside {1,...,s-2}.

In the nonintegral case its p-valuation is exactly -1. This is an
all-index statement about the polynomial moments, not an extrapolation.

In particular, if L<(s-1)(p-1), then 1<=k<=s-2 whenever (p-1)|L,
so the factor L+k=kp cancels the Bernoulli denominator. Consequently

    p > max(s, 1+(2E+2)/(s-1))
    implies every mu_s(t^e), 0<=e<=E, is p-integral.

For K=40n, N=3n and E=K+4N-2, this threshold is

    p > max(s, 1+((13/5)K-2)/(s-1)).

For weight seven, it is asymptotically (13/30)K, rather than K.
For weights five and nine, the corresponding slopes are 13/20 and 13/40.
This sharpens the polynomial-moment ingredient in the smaller-prime bands.
It does not remove the harmonic pole denominators or interpolation-node
collisions of the full Hankel matrix.

## No new polynomial-moment denominator cost at higher weights

There is a stronger direct comparison. For fixed integer s>=5 set
C_s=(s-1)!/24, an integer. The moment formula gives the exact identity

    C_s mu_s(t^e) = product_(j=6..s)(2e+j) mu_5(t^e).

The product is empty at s=5. In particular, at weight seven,

    30 mu_7(t^e) = (2e+6)(2e+7) mu_5(t^e).

Thus the reduced denominator of each mu_s(t^e) divides C_s times the
denominator of mu_5(t^e). Taking least common multiples over any growing
degree interval proves D_s(E) | C_s D_5(E). This is uniform in E, with a
constant depending only on the fixed weight. The polynomial moments
alone therefore incur no positive quadratic-scale denominator penalty
when raised from weight five to s.

This controls a common denominator of the moments. It does not bound
the relative primitive monic Hankel denominator d_s/d_5: its content
also depends on cancellations among determinant coefficients. Integer
multipliers varying with e can change those cancellations. The rational
pole moments also change, so the full transfer still requires the local
characteristic-polynomial estimate identified in the newer chats.

Reference for the denominator input:
https://dlmf.nist.gov/24.10

## Exact verification and formal scope

The checker reconstructs Bernoulli numbers by their defining rational
recurrence, then tests the support criterion against the reduced rational
moment denominators for weights 5,7,9,11,13 at K=80,N=6, degrees 0 through
102 and all relevant primes greater than the weight.

The Lean module HankelMomentCutoff proves the all-index arithmetic
cancellation-factor lemma and its contrapositive cutoff. It does not
yet formalize the complete Bernoulli-to-moment integrality theorem.
It also verifies the exact weight-seven polynomial moment multiplication
identity (with the Bernoulli value as a rational parameter), and the
general reduced-denominator consequence of an integer weight-raising
identity. All four declarations compile. Their dependency report is
saved alongside the manuscript verification logs. The full Bernoulli
support result above remains a paper application of von Staudt-Clausen.

## Attempt to finish using the weight-five method

The latest Hankel chat uses primitive monic denominators d_(s,6), and
the remaining transfer cost is

    limsup K^(-2) log(d_(s,6)/d_(5,6)).

The weight-five source was checked against the Archive of Formal Proofs
entry and the locally available mo271/Zeta5 source. This continuation
does not claim a fresh build of that separate formalization:
https://isa-afp.org/entries/Zeta_5_Irrational.html

The reported large-prime estimate above K is 9/640 at this scale. Even
accepting that estimate, it exceeds the conservative weight-five margin
0.0035 reported in that chat. The smaller-prime part is therefore still
needed. Its sign is not determined by the new polynomial-moment cutoff:
harmonic and collision terms remain. The chat's finite exact relative
denominator measurements, about 0.75 to 0.96 for the small cases shown,
also do not establish the required small asymptotic rate.

The earlier sine-filter result controls the size of raw Plücker minors.
It does not supply the missing primitive denominator estimate for this
different Hankel family. Likewise, the Hodge conductor and counting
identities do not prove nonescape for the prescribed deterministic slope.

Thus neither an individual weight-seven irrationality proof nor the
all-odd theorem follows from the presently verified estimates. The
new result here is the exact polynomial-moment denominator support and
its smaller prime cutoff. No final irrationality theorem is added as a
Lean assumption or as a manuscript conclusion.
