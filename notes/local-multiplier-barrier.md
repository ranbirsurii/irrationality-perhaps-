# A shrinking-disk maximum for the actual signed multiplier

Let n,m be nonnegative integers and define

    C_(n,m)(z) = sum_(j=0..m) (-1)^j binom(n+2m+1,m-j) binom(n+j,j) z^j.

The following estimates hold at all indices, not by finite extrapolation.
They control this polynomial, rather than the selected integer-form cost.

## Exact maximum on a disk around the cancellation point

The already proved signed moment identity gives the exact Taylor expansion

    C_(n,m)(1+w) = sum_(k=0..m) (-1)^k M_k w^k,
    M_k = binom(n+k,k) binom(2m-k,m-k) > 0.

For every rho >= 0, the triangle inequality gives

    max_(|z-1|<=rho) |C_(n,m)(z)|
       = sum_(k=0..m) M_k rho^k = C_(n,m)(1-rho).             (1)

Equality is attained at the real point z=1-rho. Thus this is an exact
maximum, with no unproved assertion about an optimal contour.

For 0<=k<=m, cancellation of factorials yields

    binom(2m-k,m-k)/binom(2m,m)
       = product_(j=0..k-1) (m-j)/(2m-j) <= 2^(-k).          (2)

For m=0 only k=0 occurs and the empty product is one. For m>0 every
denominator in the displayed product is positive. Therefore, for 0<=rho<2,

    max_(|z-1|<=rho) |C_(n,m)(z)|
       <= binom(2m,m) sum_(k=0..infinity) binom(n+k,k)(rho/2)^k
       = binom(2m,m) (1-rho/2)^(-(n+1)).                    (3)

The last identity is the ordinary negative-binomial series.
Set N=n+1 and rho=1/N. Bernoulli's inequality gives

    (1-1/(2N))^N >= 1-N/(2N) = 1/2.

Combining with (3) proves

    max_(|z-1|<=1/(n+1)) |C_(n,m)(z)| <= 2 binom(2m,m).     (4)

## Explicit decay at the critical exponential normalization

An elementary central-binomial bound is

    binom(2m,m) <= 4^m / sqrt(3m+1).                        (5)

For completeness, square and normalize by 16^m. The ratio of consecutive
squared normalized binomial coefficients is ((2m+1)/(2m+2))^2. The induction
step follows from the exact nonnegative difference

    (2m+2)^2(3m+1) - (2m+1)^2(3m+4) = m.

The base case m=0 is equality. Hence for fixed r>=0 and n>=r, setting m=n-r
in (4)-(5) proves

    4^(-n) max_(|z-1|<=1/(n+1)) |C_(n,n-r)(z)|
       <= 2*4^(-r)/sqrt(3(n-r)+1) -> 0.                    (6)

This is a genuine all-index decay result for the normalized local polynomial
maximum. It uses a polynomial saving at the critical exponential rate;
it does not claim a strictly negative normalized logarithmic rate.

## Integral interpretation and scope

Direct expansion and the beta integral also give

    C_(n,m)(z) = (n+2m+1)!/(n! (m!)^2)
                * integral_0^1 t^n (1-t)^m (1-zt)^m dt.      (7)

Indeed the coefficient of z^j follows by integrating t^(n+j)(1-t)^m.
This is the terminating Euler hypergeometric integral. It identifies an
actual analytic object to which a maximum argument applies; no minimal
surface or elliptic PDE is introduced.

The full cancellation forms involve varying branch amplitudes and Laurent
coefficient functionals, not only the scalar value C(z). In particular a
representation as C(z) on the disk in (6), with a sufficiently bounded
prefactor and the required integral normalization, has not been proved
for the continued-fraction interval cost E_n. Thus (6) cannot yet be
substituted for E_n. The all-odd irrationality conclusion remains unproved.

The script check_local_multiplier_barrier.py independently checks the
moment expansion, equality in (1) at rho=1/(n+1), the factor estimate (2),
the rational version of (4), and the squared versions of (5)-(6) at all
861 profiles 0<=m<=n<=40. These finite checks supplement the all-index
proof above; they are not a Lean formalization of it.
