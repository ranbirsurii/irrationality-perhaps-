# A unified subunit certificate and the precise rate boundary

The construction below proves negative unscaled logarithms at every
fixed odd weight s>=7 and every eligible index, by adapting the finite
prefix cutoff. It proves a nonpositive normalized upper logarithmic
rate, not the strictly negative rate needed for exponential decay.

## The rational stopping rule

Keep the original Padé blocks, coefficient lattice, primitive coefficient
pairs and signed-prefix majorant. Only the cutoff K is chosen adaptively.
Fix s=2r+1>=7 and even n>=2r. Write

    P=sum_(m<k<=K)T(k),  T0=tau_0,  mu=P+T0,
    Q=H+q*q^T/P,

where H is the raw, denominator-cleared tail matrix, and q is the raw
signed-prefix coefficient row. Thus the complete squared certificate
for a pair y is mu*y^T Q y. All entries are rational and computed without
evaluating zeta.

Use the unimodular coefficient basis y_1=(1,-1),
y_2=(2^s,-2^s-1), whose determinant is -1. Set

    B=(3/2)*(2/3)^s,  delta=B^2/16,
    H_i=y_i^T H y_i.

Starting with K=2n, double K until the tail power is admissible and

    T0/P <= delta,   mu*max(H_1,H_2) <= delta^2.       (A)

These are exact rational comparisons. The rule neither assumes
irrationality nor tests a numerically evaluated linear form for zero.

## Termination, for every index

For fixed s,n, the rational kernel has decay order

    E=s(n+1)-2(n-r)=(2r-1)n+4r+1>4r+2.

The exact logarithmic-derivative budget used in the preceding note tends
to E as K tends to infinity. Consequently its integer tail power is at
least E-1 eventually. Formula (3) of the signed-prefix note gives

    tau_j=O_(s,n)(K^(-E+2j+1)),  0<=j<=2r.

Each tail majorant tends to zero. The fixed rational profile map then
gives H_i->0. Also P tends to the positive convergent total kernel mass,
and mu tends to that same mass. Both left sides of (A) tend to zero.
The doubling search therefore terminates at every eligible index.
The constants in this termination proof may depend on s and n; no
unproved estimate on how large the terminating K must be is used.

## The complete all-index bound

The two integer forms are positive Dirichlet tails:

    zeta(s)-1=sum_(k>=2) k^(-s)>0,
    2^s*zeta(s)-(2^s+1)=sum_(k>=3) (2/k)^s>0.

Integral comparison proves

    zeta(s)-1 <= 2^(-s)*(1+2/(s-1)) <= (4/3)*2^(-s) <= B,
    2^s*zeta(s)-(2^s+1) <= (2/3)^s*(1+3/(s-1)) <= B.

The comparison of the first bound with B uses
(8/9)*(3/4)^s<=1. Both forms therefore have absolute value at most B,
with no irrationality assumption. For all s>=7, 0<B<=64/729<1.

Let a_i=q*y_i be their signed-prefix values and b_i the actual tails.
The established tail Cauchy inequality and (A) show

    b_i^2<=T0*H_i<=mu*H_i<=delta^2,
    |a_i|<=B+delta,  mu/P<=1+delta.

Since delta<=1, mu*H_i<=delta^2<=delta. The prefix majorant therefore
has the explicit bound

    mu*y_i^T Q y_i
      <=(1+delta)*(B+delta)^2+delta
      <=2B^2.                                       (B)

For completeness, 0<B<=1 gives delta<=B/16 and delta<=1/16.
Thus (1+delta)(B+delta)^2+delta
<=((17/16)^3+1/16)*B^2<=2B^2. Lean verifies this margin.

The second binary minimum is at most the larger value on any unimodular
basis. Thus the Gauss-reduced complete cost R and its scalar sandwich C
satisfy, at every index using the terminating cutoff,

    0<C<=R<=(9/2)*(4/9)^s<1/64.                    (C)

This is a genuine all-index bound, obtained from a finite rational
stopping rule. It changes the cutoff of the certificate, not the kernel
or the cancellation lattice. It does not assert that a fixed earlier
cutoff, such as 6n, always satisfies (A).

## What this proves about the common logarithm

Equation (C) proves

    log C<=log R<=log(9/2)+s*log(4/9)<-log(64)<0.

Together with the proved O(1/n) logarithmic sandwich gap it proves

    limsup log C/n = limsup log R/n <= 0.

The bound is uniform in the weight as well as the index, although the
terminating cutoff depends on both. The upper limits may be read in
the extended reals. Strict negativity
of this normalized common rate has not been proved. A constant cap
below one does not tend to zero. Consequently (C) does not supply the
irrationality conclusion; it establishes the boundary value available
without a further quantitative integer-selection estimate.

## A direct arithmetic shortcut was also tested

For a rational binary form with coefficients A,2B,C, let d clear their
denominators and let eta=gcd(dA,2dB,dC)/d. Each nonzero integer value is
at least eta, so alpha>=eta and

    R <= (4/3)*mu*det(Q)/eta.

This is a rigorous purely arithmetic upper bound with no unknown minimum.
However its finite logarithmic costs were positive in the tested weight-
seven cases: approximately 15.55 to 78.32 per index across the tested
cutoffs. It therefore did not establish the needed negative rate. These
finite failures are not extrapolated into an asymptotic impossibility.

## Formal and computational scope

Lean checks eight new implications: the adaptive quadratic bound, a
basic unit margin, neighboring integer-form bounds, negative unscaled
logarithms, a nonpositive normalized upper-rate envelope from bounded
positive cost, the stronger seed margin, and the uniform geometric-weight
1/64 cap, and the explicit log R < -log(64) inequality. The rational stopping-rule termination, zeta integral comparison,
and actual profile identification are paper proofs above, rather than
being silently included in the Lean statements.

The script verifies (A) and (B) exactly in twelve cases across weights
7,9,11,13,15,17,21, reaching n=160 at weight seven. All twelve stop at
K=2n. This finite observation is not a proof that 2n always suffices.
