# Large-index bounds for the actual little gamma and epsilon

This note concerns the exact weight-five three-block construction used
in the bound with d_n^5. All limits below are along even n. No finite
sample is used to infer an asymptotic rate.

Define

    gamma_lower = liminf log(Gamma_n)/n,
    epsilon_upper = limsup log(kappa_n H_n)/n,
    H_n=||x_n/g_n||_2,   kappa_n=lambda_2/lambda_1.

Existence of separate ordinary limits is not assumed.

## What the established all-index estimates prove

The proved row recurrence and lower-column prime divisor estimate give

    limsup log(H_n)/n <= b=5+(1/2)log(rho)-c_g,
    c_g=3+pi/(4sqrt(3))+(3/4)log(3),

where rho is the largest root of
z^3-30510z^2+15146217z+729. The root bounds are
30005<rho<30006. Exact constant enclosures in
`row-balance-rate-budget.json` give b<5.877168; the stored upper
endpoint is 5.877167262765. These are enclosures of constants,
not a fit to a sequence. See `row-balance-and-kappa.md` for the
recurrence and `lower-column-prime-divisibility.md` for the divisor.

Take an integral Gauss-reduced kernel basis with Gram entries A,B,C.
Saturation gives AC-B^2=H_n^2, while A>=1 and |B|<=A/2. Therefore

    kappa_n^2=C/A=H_n^2/A^2+(B/A)^2 <= H_n^2+1/4.

Since the primitive integer normal has H_n>=1,

    kappa_n H_n <= (sqrt(5)/2) H_n^2.

Taking logarithms and upper limits proves the actual asymptotic bound

    0 <= epsilon_upper <= 2b <= 11.754334525530 < 11.754335.

The lower bound follows from kappa_n>=1 and H_n>=1. The harmless
constant sqrt(5)/2 disappears after division by n.

For the image content, full rank makes Gamma_n a positive integer.
The subsequent all-weight argument in `image-content-prime-divisor.md`
strengthens the earlier trivial lower bound to

    gamma_lower >= pi/(4sqrt(3))+(3/4)log3-1/2
                   =0.777409057559... .

This is a lower bound, not an asserted value of gamma_lower. In particular,
the proved constant c_g is a lower bound for the different lower-row gcd
g_n, not for the coefficient-image content Gamma_n. It has already been
used in H_n and cannot be counted a second time as a bound for Gamma_n.

## Consequence for the requested conclusion

The available unconditional bounds are too weak to make

    5-gamma_lower+epsilon_upper/2

negative, even after the known raw analytic decay is included. They do
not prove gamma_lower>5.12 or epsilon_upper<0.24.

The earlier prime-density discussion proposes
(3/2)(1+log(3)) approximately 3.147918433 as a possible content lower
rate. Its required aggregate image-content divisibility estimate is
unproved; this number is not an established asymptotic value of gamma.
Neither can the finite epsilon values be called a limit.

Thus these are genuine large-n bounds, but not the sharp bounds needed
to complete the irrationality argument. The all-odd irrationality
conclusion remains unproved. The newer clearing-free moment method is
an alternative formulation and does not acquire a proved rate from
these weight-five constants.

## Separate finite calculation

`gamma_epsilon_rates.py` independently checks the stored image gcd and
saturated Gram determinant identities and encloses gamma_n and epsilon_n
with rational logarithm intervals. Those records are in
`gamma-epsilon-rates.json`. They are kept separate from the asymptotic
bounds above. In particular, they do not establish the existence or
values of the infinite-index limits.
