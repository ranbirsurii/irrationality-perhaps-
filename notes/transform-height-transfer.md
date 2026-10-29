# Sharper multiplier bounds and their exact transfer to the actual normal

The proposed proportional-offset improvement is valid for the integer
transformation multipliers. This note improves that bound further and
computes the map to H_n explicitly. It does not identify these two
different heights or assert a new asymptotic Gamma bound.

## A better bound for the multipliers

Retain c_j=(-1)^j binom(n+2m+1,m-j)binom(n+j,j) and W=sum|c_j|.
For every real 0<z<1, coefficient positivity gives

    W <= E(z)=(1+z)^(n+2m+1)/[(1-z)^(n+1)z^m].

When m>0 the minimizing radius is explicitly

    z_* = m/[n+m+1+sqrt((n+1)(n+2m+1))].

Indeed the logarithmic derivative, multiplied by z(1-z^2), is
-m+2(n+m+1)z-m*z^2. It is strictly increasing on (0,1), changes
sign once, and its zero is the displayed z_*. If m=0, W=1 exactly.

There is also an explicit inverse-square-root improvement. Put
N=n+2m+1 and p=z/(1+z). Normalize the generating function at radius z.
Its coefficient probability is that of X+Y, where X is binomial(N,p)
and Y is the independent sum of n+1 geometric variables with probability
generating function (1-z)/(1-zt). Thus

    W=E(z)*Pr(X+Y=m) <= E(z)*max_k Pr(X=k).

Fourier inversion for X gives

    max_k Pr(X=k)
      <= (1/(2*pi)) integral_(-pi..pi)
           |1-p+p*exp(it)|^N dt
      <= sqrt(pi/[8N*p*(1-p)]).

For the second inequality use |1-p+p*exp(it)|^2
=1-4p(1-p)sin(t/2)^2, log(1-u)<=-u, and
sin(|t|/2)>=|t|/pi on [-pi,pi], then extend the resulting Gaussian
integral to the real line. Consequently the finite-n bound is

    W <= E(z)*min(1,sqrt(pi*(1+z)^2/[8N*z])).

Every rational z is allowed. The checker encloses sqrt((n+1)N) by
integer square roots to select a rational radius near z_*, and replaces
pi by the rigorous upper bound 22/7. All numerical certificates remain
rational. No sampling of a complex contour is used.

At the earlier radius z0=2-sqrt(3), with offset h=n-m, this gives

    W <= (sqrt(3)/6^h)*(6sqrt(3))^n*sqrt(3*pi/[4(n+2m+1)]).

In particular the following stronger integral inequality holds:

    14(n+2m+1)6^(2(n-m)) W^2 <= 99*108^n.

## Improved asymptotic multiplier rate for proportional offsets

If m_n/n -> beta in (0,1], the optimal-radius upper rate is

    limsup log(W_(n,m_n))/n <= b(beta),
    z_beta=beta/[1+beta+sqrt(1+2beta)],
    b(beta)=(1+2beta)log(1+z_beta)-log(1-z_beta)-beta*log(z_beta).

This is at least as strong as using the same radius z0 at all beta.
For example beta=1/2 gives b(beta)=log(4), improving the previous
log(6sqrt(3))-(1/2)log(6). For a fixed offset h, beta=1 and the rate
remains log(6sqrt(3)); the new improvement there is polynomial.

More explicitly, when n is even and m=n/2 choose z=3-2sqrt(2).
Then E(z)=sqrt(2)*4^n and p(1-p)=1/8. The finite bound becomes

    W_(n,n/2) <= sqrt(2*pi/(2n+1))*4^n,
    7(2n+1) W_(n,n/2)^2 <= 44*16^n.

The second inequality uses pi<22/7 and is checked with integers.

The coefficient offset h=n-m is independent of the zeta half-weight
r_w=(s-1)/2. One can vary numerator length at fixed weight. Setting
r_w proportional to n instead would vary the target zeta value and
would not establish a theorem for each fixed weight.

## Exact map to H_n

For the original weight-five three-block family, let m_i=n-i,
c_(i,j) be the above multipliers, and R_(i,j) the transformed rational
blocks from `saalschutz-kernel-transform.md`. Define

    P_n=max_(i,j)|a_3(R_(i,j))|,
    W_n=max_i sum_j |c_(i,j)|,
    D_n=lcm(1,...,n)^5, g_n=gcd(x_0,x_1,x_2).

Linearity of the third-order Laurent coefficient sum proves exactly

    H_n=(D_n/g_n)*||(sum_j c_(i,j)a_3(R_(i,j)))_(i=0..2)||_2,
    H_n <= sqrt(3)*(D_n/g_n)*W_n*P_n.

This includes the branch coefficient map, not just its multipliers.
The new bound for W_n therefore does not alone replace the established
5.877168 upper rate for H_n by 2.341066. The branch functions contain
their own factorial normalization and Laurent coefficients.

The independent branch calculation expands each rising-factorial
numerator through degree two at every pole and multiplies by the exact
regular-denominator Taylor jet. It recovers all three original a_3
coefficients exactly at n=12,20,40. The direct inequality H_n<=W_n
fails at those indices, while the displayed full transfer bound passes.
These finite checks do not disprove a proposed asymptotic rate; they
verify which map factors must be included when trying to prove it.

## Joint numerator-length tests at fixed weight

The moment checker now accepts an independent numerator length B in
r_w<=B<=n, using blocks B,B-1,...,B-r_w. It reconstructs the primitive
integer pair, inverse coefficient profiles, moment matrix and infinite
tail certificate for each choice. Thus it tests the complete bound,
including the changed analytic decay, rather than W alone.

At (s,n)=(7,20),(7,40),(9,24), the tested lengths are
r_w, floor(n/2), floor(3n/4), n-2, n-1, n. In each group B=n gives the
smallest complete moment bound among those tested lengths. These are
finite comparisons, not an all-index optimality theorem.

The improved multiplier inequalities pass all 120 existing polynomial
test cases. The 360 independent beta-integral checks and 48 exact
hypergeometric term checks still pass. Eighteen earlier transition-norm
checks and three default-family regressions also pass after the optional
length parameter was introduced.

No new lower rate for the image content Gamma_n has been proved by
these calculations. A binomial expression permits explicit valuation
work; it does not by itself establish the valuations after the actual
integral projector and its gcd normalization. The all-odd irrationality
claim remains unproved. The manuscript is not rewritten in this pass.
