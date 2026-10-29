# A sufficient target for every odd weight and arbitrary admissible weights

This note formulates and proves a sufficient criterion. It does not
prove that the actual family satisfies the criterion.

Fix any odd s=2r+1>=7. All index limits below may be restricted to any
unbounded sequence of even n>=2r. Let C be the cleared lower-period
matrix, let Lambda=ker_Z C, and let Y,Z be the target and constant rows.
The established full augmented rank makes Lambda a saturated rank-two
lattice and the target-and-constant map injective on its rational span.
Set D_n=lcm(1,...,n)^s and

    A_s=log(2397)+(s-7)log(4).

The proved fixed-weight moment estimate, applied to each coordinate
block, gives for S_n=max_(j=0..r) A_(s,n,n-j)

    S_n <= B_s (n+1)^(2s+2) exp(-A_s*n)

for a fixed positive B_s. For instance the weighted profile estimate
with a coordinate vector permits B_s=56^r C_s using the C_s in the
parametric moment proof. The polynomial and B_s have zero logarithmic
rate at each fixed s.

## Arbitrary selected weights with their individual contents

Choose any two independent integer vectors w_1,w_2 in Lambda; they
need not be a Gauss basis or have positive coordinates. For i=1,2 put

    h_i=gcd(Y(w_i),Z(w_i))>0,
    L_i=(Y(w_i)/h_i)*zeta(s)+Z(w_i)/h_i,
    Theta_n=max_i ||w_i||_1/h_i.

The coefficient divisions are integral. Independence and full rank
make their two target pairs independent, so L_1 and L_2 cannot both
vanish for any real number substituted for zeta(s). Direct evaluation
and the triangle inequality give

    max_i |L_i| <= D_n S_n Theta_n.

Consequently the sufficient arbitrary-weight target is

    limsup log(Theta_n)/n < A_s-s.                         (T)

Proof: log(D_n)/n -> s. The upper rate of the complete right-hand
side is at most s-A_s+limsup log(Theta_n)/n<0, so both forms tend to
zero. If zeta(s)=p/q, every nonzero integer-coefficient form has
absolute value at least 1/|q|. One of the selected pair is nonzero
at each index, which gives the contradiction.

Rational block weights are also covered: clear their coordinate
denominators to obtain integer w_i. The ratio ||w_i||_1/h_i is unchanged
by further positive integer scaling. Neither an omitted clearing
denominator nor an assumed nonzero individual form is used here.

## A joint arithmetic/geometric target at arbitrary odd weight

Let a,b be an integral Gauss-reduced basis of Lambda, and let lambda_2
be its longer length. Let Gamma be the gcd of all four target and
constant coefficients Y(a),Y(b),Z(a),Z(b). Then h_i>=Gamma, and
||w_i||_1<=sqrt(r+1)*lambda_2 for this basis. Thus a sufficient special
case of (T) is

    liminf [log Gamma_(s,n)-log lambda_(2,s,n)]/n > s-A_s. (J)

Equivalently, with H=covol(Lambda) and kappa=lambda_2/lambda_1,
the reduced angle lies between pi/3 and 2pi/3 and

    log(lambda_2)=(log(kappa)+log(H)-log(sin(angle)))/2.

The angular term divided by n tends to zero. Therefore (J) is exactly
the sufficient correlated target

    liminf [log Gamma-(1/2)log kappa-(1/2)log H]/n > s-A_s.

Separate bounds gamma_s=liminf log Gamma/n and
epsilon_s=limsup log(kappa*H)/n suffice if

    gamma_s-epsilon_s/2 > s-A_s.

The correlated version may be stronger than subtracting separate
limits; it does not require the existence of either ordinary limit.
These targets concern complete primitive forms, not decay of the
arithmetic cost alone before the analytic factor is included.

## A particularly simple uniform sufficient target

For every s>=7, A_s-s>3/4. The Lean proof uses rational lower
bounds for log(5/4), log(6/5), log(7/6), log(8/7) and
log(2397/2048); their sum proves log(2397)>31/4.
The positive slope log(4)-1 makes the allowance increase with s.
Thus one sufficient concrete target at every odd weight is

    Theta_(s,n) <= exp(3n/4) eventually,                  (U)

or, using a reduced basis and allowing the harmless fixed-dimensional
norm factor,

    Gamma_(s,n) >= exp(-3n/4)*lambda_(2,s,n) eventually.  (U')

The net upper exponential rate is at most s+3/4-A_s<0. Allowing small
error envelopes from the prime number theorem and the fixed polynomial
still leaves a strictly negative rate. The same assertion along an
unbounded eligible subsequence suffices at each weight.

More generally, for any chosen real eta_s<A_s-s, one may replace 3/4
by eta_s. Equivalently allocate any fraction t in [0,1) of the allowance:
eta_s=t*(A_s-s). This gives the weighted tradeoff
Gamma/lambda_2 >= exp(-eta_s*n), with positive rate remaining.

No condition (T), (J), (U), or (U') has been proved for the actual family
here. These are sufficient targets with their implications proved,
not unconditional irrationality theorems.

## Direct transfer through the lower coefficient volume

Let C=D_n C_raw, let g be the gcd of the maximal (r-1)-row minors
of C, and let V=sqrt(det(C_raw*C_raw^T)). The primitive Plucker
coordinate formula gives

    H=D_n^(r-1)*V/g.

Substituting lambda_2=H/(lambda_1*sin(angle)) in the complete bound
gives another sufficient arbitrary-weight formulation:

    liminf log(Gamma*g*lambda_1/V)/n > r*s-A_s.

This retains the signed lower-row volume rather than bounding all
transformation multipliers independently. It is the same target in
construction-specific quantities. No growth estimate for that joint
quantity is inferred from rank or from the identity alone.

## Verification scope

The Lean additions prove the abstract smallness implication with any
allowed exponential cost eta satisfying sigma+eta<decay, and the
uniform A_s-s>3/4 allowance. The actual-family rank, Plucker and
primitive-form identifications remain paper arguments.
`arbitrary_weight_targets.py` encloses illustrative thresholds with
rigorous rational logarithms; it does not sample family matrices or
infer that any sufficient target holds.
