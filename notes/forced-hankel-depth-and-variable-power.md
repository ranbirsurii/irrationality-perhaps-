# Large-prime depth and a weight-dependent Hankel family

No finite-index experiments were run for this continuation. The work starts
from the exact Lagrange representation of the current powered Hankel family.
The full derivation is in publication/high-weight-criterion/forced-hankel-depth.tex.

## A calculated local coefficient, not a hypothetical growth assumption

Let K=40n, N=3n, h=37n, and P_s=Delta_s/L_s for the existing sixth-power
family. Fix odd s>=9. For sufficiently large K and every prime
2K/3<p<K, set m=K-p+1. Then

    v_p([X^(h-m)] P_s) = -s*m.

In particular, the actual primitive denominator satisfies

    p^(s*m) | d_(s,6)(K).

This follows from an explicit congruence, after a rational similarity
transform of the Lagrange-basis constant matrix:

    p^(s*h) P_s(X/p^s)
       = X^(h-m) (X-1/2) (X-1)^(m-1) modulo p.

The boundary entry i=p contributes -1/2, not -1. This term includes
the rational 1/(2i) part of the pole moment.

The proof has two separate checks of the coefficient: polynomial
multiplication, and the unique nonzero elementary symmetric term of
order m in the diagonal reduction. No eigenvalue asymptotic or numerical
evidence is substituted for the congruence.

The local polynomial term is integral after multiplication by p^s:
its unscaled row valuations are at least -7 outside i=p and -(s-1)
at i=p. This uses the exact Bernoulli moment cutoff, integer polynomial
quotients, at most three representatives of a square class, and the
fact that at most one numerator root matches a nonzero square class.

Partial summation gives the all-index consequence

    liminf log d_(s,6)(K)/K^2 >= s/18.

At weight seven p^7 times the constant matrix is still integral.
Only rows whose numerator root matches modulo p can have a nonzero
polynomial correction. Reordering those rows first makes the reduction
block triangular. The remaining active good rows give

    p^(7*(max(0,K-p-N)+1)) | d_(7,6)(K),
    liminf log d_(7,6)(K)/K^2 >= 6727/28800.

The manuscript gives the block-triangular coefficient argument explicitly.
This is a lower bound on arithmetic cost, not the missing upper bound.

An intentionally coarse upper bound at weight five is

    limsup log d_(5,6)(K)/K^2 <= 139/4.

Its proof uses the previously established all-prime clearing factor
lcm(1,...,5K)^(6h)*24^h, Stirling's formula for the explicit basis
normalization S_K, and the bound log|L_5| <= (10Nh+4h)log K.
Consequently

    liminf log(d_(s,6)/d_(5,6))/K^2 >= s/18 - 139/4.

Therefore a single fixed finite transfer margin cannot cover all odd
weights in the unchanged sixth-power family. This does not disprove
irrationality, nor does it exclude a weight-seven transfer. It identifies
a necessary change for this particular route to an all-weight theorem.

## Constructed replacement family

Work backwards from the source of the increasing pole order, and use

    DeltaTilde_s(X) = det[mu_(s,X)(D_N(t)^(s+1)*t^(i+j)/D_K(t))].

This equals the weight-five construction at s=5. It has degree h,
leading coefficient

    (-1)^(h*(h-1)/2) * product_(j=N+1..K) j^(s-1)*D_N(-j^2)^s,

and polynomial quotient degrees at most K+(s-1)N-2. At X=zeta(s)
the same positive density gives a strictly positive Gram determinant.
The preceding automatic pole-dominance calculation no longer applies:
the numerator root multiplicity now grows with s as well.

This constructs a different family; it does not establish a negative
total rate. Its local allocation and archimedean energy must both be
proved for these parameters. The weight-five numerical margin has not
been reused for a changed family.

## Recent literature checked

The AFP entry dated October 26, 2026 describes a formal proof of zeta(5)
irrationality using positive Hankel polynomials, prime allocations and
a logarithmic-energy bound:
https://isa-afp.org/entries/Zeta_5_Irrational.html

The existing local copy of domino14/zeta5 was read, particularly
Apery/Arith/OuterEntryMain.lean, OuterBasis.lean, InnerAlloc.lean,
Norm.lean, and the prime-allocation tables. It was not rebuilt here.

The abstract and opening material of OpenAI's September 30, 2026
Quasi-Riemann Hypothesis preprint were read directly from its PDF:
https://github.com/openai/math/blob/main/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf

It states a zero-free half-plane for Dirichlet and specified Hecke
L-functions. No entire-paper verification is claimed. A stronger
prime-summation error estimate cannot change the nonzero coefficient
above or the leading PNT integral. No estimate from that preprint is
imported as a Lean axiom.

The introduction of OpenAI's September 24, 2026 Catalan preprint was
also read directly. It uses mixed signed determinants, separate p^2
and p valuation layers, arithmetic nonvanishing at prime scales, and
holomorphic interpolation for its real-place bound. Its determinant
entries and their cancellation identities concern beta(2), not the
present zeta(s) family. No unsupplied identification or denominator
transfer is assumed:
https://github.com/openai/math/blob/main/preprints/Catalans-constant-is-irrational-September-24-2026/paper.pdf

## Formal scope

OddZeta/HankelForcedDepth.lean verifies four general algebraic lemmas:
negative valuation forces a prime power in a reduced denominator;
a unit coefficient after root scaling gives that denominator divisor;
the terminal reduced polynomial has the claimed coefficient; and
the i=p boundary identity is exact.

The Lagrange specialization and prime asymptotic remain paper proofs.
No completed Lean proof of irrationality or of the entire local
specialization is claimed. The target all-odd irrationality theorem
remains unproved.
