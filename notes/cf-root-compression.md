# Continued-fraction compression of the cofactor roots

This is a concrete change in the selected integer forms. It truncates
the cofactor-root approximants instead of using their full numerators
and denominators. The finite improvement is substantial; no uniform
irrationality conclusion is inferred from it.

Subsequent update: `recentered-cf-root.md` absorbs the exact signed
prefix into the rational centre. This supplies uniform accuracy at any
prescribed geometric precision for the corrected centres. Their
continued-fraction denominator gaps and a uniform decay estimate for
the resulting integer forms remain to be controlled.

## A certified rational approximation, without knowing irrationality

At each eligible index, choose a nonzero entry V_j of the constant
adjugate column. Such an entry exists because the augmented matrix is
invertible. Put g=gcd(U_j,V_j), p0=-V_j/g, q0=U_j/g. In particular
p0!=0. The signed-prefix construction gives a positive rational R0 with

    |p0 zeta(s)+q0|<=R0.

If necessary enlarge R0 to max(R0,4^(-n)) to ensure positivity.

Define the rational numbers sigma=-q0/p0 and delta=R0/|p0|. Then

    |zeta(s)-sigma|<=delta.                                  (1)

The root selection, cutoff, and R0 use only rational kernel data. The
independent zeta enclosures in the script validate them; the enclosures
are not used to select the continued fractions.

## Two independent compressed forms

For any consecutive convergents P0/Q0 and P1/Q1 of sigma, include
the initial 1/0 when appropriate. The denominators are nonnegative and

    |P0 Q1-P1 Q0|=1.

Consequently their primitive integer forms

    L_i=Q_i zeta(s)-P_i

cannot both vanish, for any real value of the target. Indeed subtracting
Q0 L1 from Q1 L0 gives P1 Q0-P0 Q1=+1 or -1. There is no assumption
of irrationality in this argument.

The exact triangle inequality gives the computable common upper bound

    |L_i|<=|Q_i sigma-P_i|+Q_i delta,
    E(pair)=max_(i=0,1)(|Q_i sigma-P_i|+Q_i delta).             (2)

Minimize this rational E over all consecutive pairs in the finite
continued fraction of sigma. This includes terminal pairs, so no
unproved assertion about a nonterminal bracket is used. The minimum
exists and is positive since delta>0. Let E_n be its value.

For every actual eligible index, (1)-(2) therefore prove

    exists integers p,q: 0<|p zeta(s)+q|<=E_n.                (3)

Classical choice may legitimately select a nonzero member of the pair
in (3), because its existence has just been proved by the unit
determinant. This does not assume the separate claim E_n->0.
The new Lean theorem nonzero_small_form_of_independent_slope_pair
verifies this existence implication from the approximation and pair
bounds. The rational-error transfer is proved separately in
slope_error_transfer.

There is also a finite certificate for the nonzero selection: use
signed-prefix errors at most min(E_n/16,1/(8(Q0+Q1))). If both prefix
intervals contained zero, both actual forms would have absolute value
at most 2/(8(Q0+Q1)), contradicting the unit determinant. Hence one
interval excludes zero. Cutoff refinement terminates by the previous
tail bound, so this alternative does not require deciding equality of
real numbers.

## What would give a proof at all large indices

Let V=max(Q0,Q1) for any consecutive pair. The usual continued-fraction
error bounds, including the terminating case, give

    E(pair)<=1/V+V delta.                                   (4)

Hence it is sufficient to prove delta_n<=C exp(-c n) and to produce
consecutive pairs whose maximum denominator satisfies

    exp(a n)<=V_n<=exp(b n), 0<a<=b<c.

Equation (4) then proves

    E_n<=exp(-a n)+C exp(-(c-b)n)->0.

This uses the certified cofactor-root accuracy rather than the previous
fixed 4^(-n) metric scale. It can permit a larger denominator-growth
window. Neither a uniform root-accuracy rate c nor the needed uniform
denominator window is proved by the finite table below. Directly proving
E_n->0 would suffice and would avoid splitting it into those two rates.
This remains the original arithmetic approximation problem in sharper
coordinates, not a new independent hypothesis supplied as a theorem.

## Exact finite certificates

The script cf_root_compression.py checks ten profiles at weights 7,9,11.
Each profile uses one root-accuracy certificate and two additional signed-
prefix certificates for the compressed pair, for thirty certificates.
The latter tail tolerances are at most E_n/16, so their common majorant is at
most 9E_n/8. Every coefficient pair is primitive, their determinant is
a unit, and independent zeta enclosures verify the signed intervals.

At weight seven, the directly certified common majorants satisfy

| n | rigorous upper bound |
|---|---|
| 6 | 9 * 10^(-9) |
| 8 | 2 * 10^(-12) |
| 12 | 4 * 10^(-21) |
| 16 | 8 * 10^(-30) |
| 20 | 3 * 10^(-37) |

These inequalities are checked by rational arithmetic, without decimal
rounding assumptions. They show that the compressed pairs remedy the
large finite forms from the full cofactor roots. They do not establish
an asymptotic law or the all-odd irrationality theorem. The full rational
kernel/continued-fraction identification is a paper argument; the two
new Lean lemmas verify the error transfer and nonzero pair selection.

Two controls distinguish valid approximation from an assumption of
irrationality. For the rational target 3/2, twelve arbitrarily accurate
rational approximants retain E>=1/2. For sixteen Pell approximants P/Q
to sqrt(2), the exact test gives E<=3/(2Q), which tends to zero along
the Pell recurrence. Thus the terminal-pair construction can support
a genuine decay proof when its quantitative input is proved, and does
not automatically invent one for a rational target.
