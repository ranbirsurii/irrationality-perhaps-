# Signed moment metric on the original family

This construction keeps the original consecutive blocks, retains the
signed polynomial cross terms, and chooses the primitive pair using a
different positive quadratic form. It supplies an all-index bound with
an explicit tail certificate. It does not prove its favorable asymptotic rate.

The quantifiers are: for every integer r>=3, every even n>=2r, and
every real coefficient pair y, the moment inequality below holds. Thus
it covers every odd weight s>=7 and every lower-period-cancelling form
in this consecutive-block span. It is not limited to the tested weights
or to the two chosen primitive forms. It does not assert an estimate
uniform in an unbounded coefficient pair without a size factor.

Fix r>=3, s=2r+1, even n>=2r, and m=n-r. Use the original common positive
kernel T=T_(s,n,m), cutoff K=3n, and w(k)=k(k+n)/(12n^2). For a coefficient
pair y=(a,b), let z=Fy be its weighted polynomial profile from the exact
transition note. Thus

    L(y)=D sum_(k=m+1..infinity) T(k) sum_(ell=0..r) z_ell w(k)^ell,
    D=d_n^s.

## Certified infinite moment bound

The logarithmic derivative bounds used in the manuscript give

    d/dt log(t^(4r+2) T(t)) <= -E/t+B/t^2,
    E=s(n+1)-2m-(4r+2)=(2r-1)n-1,
    B=2m^2+s*n(n+1),  t>=2n.

These follow directly by bounding the two numerator logarithmic
derivatives by 1/t+2v/t^2 and 1/t, and each denominator reciprocal
below by 1/t-h/t^2. The displayed B is a valid larger bound.
Here E>0 and

    EK-B=(4r-6)n^2+(2r-4)n-2r^2 > 0.

Therefore t^(4r+2)T(t) decreases beyond K. For 0<=ell<=2r, comparison
with the integral of a decreasing power gives

    sum_(k>K) T(k) w(k)^ell <= t_ell,
    t_ell=T(K) ((K+n)/K)^ell K^(2ell+1)
                /[(12n^2)^ell (4r+1-2ell)].

In particular the denominator is positive. All these upper bounds are rational.

Define the finite moments c_ell=sum_(m<k<=K) T(k)w(k)^ell, and set

    G_ij=c_(i+j)+(r+1)t_(2i) if i=j,
    G_ij=c_(i+j) otherwise,
    mu=c_0+t_0.

For any real z, the finite part of its squared polynomial moment is the
quadratic form with entries c_(i+j), retaining every signed cross term.
For the tail, (sum z_i w^i)^2 <= (r+1)sum z_i^2 w^(2i) by
Cauchy--Schwarz. Thus the complete squared moment is at most z^T G z.
The total kernel mass is at most mu. A second Cauchy--Schwarz inequality,
first on finite sums and then by the convergent moment bounds, proves

    |L(y)|^2 <= D^2 mu y^T S y,    S=F^T G F.

G is positive definite: the finite sum includes at least r+1 distinct
values of w(k) with positive weights, so a nonzero degree-r polynomial
cannot vanish at all of them. Since F has independent columns, S is a
positive definite rational binary form.

## Choosing the primitive pair

Exact binary Gauss reduction supplies U in GL_2(Z) with

    U^T S U = [[alpha,beta],[beta,nu]],
    0<alpha<=nu, 2|beta|<=alpha.

The columns y_1,y_2 of U are primitive coefficient pairs and satisfy

    max(|L(y_1)|^2, |L(y_2)|^2) <= D^2 mu nu.

Their determinant is +/-1, so the two forms cannot both vanish for any
real value substituted for zeta(s). This nonvanishing statement holds
at every eligible index and does not require a sign conjecture.

More generally every form has unique real reduced coordinates (h,k),
with y=U(h,k). The same argument gives

    |L(U(h,k))|^2 <= D^2 mu (alpha*h^2+2beta*h*k+nu*k^2)
                   <= (3/2) D^2 mu nu (h^2+k^2).

Indeed alpha<=nu and 2|beta|<=nu imply that the middle quadratic form
is at most nu(h^2+|hk|+k^2), and 2|hk|<=h^2+k^2. This proves a single
homogeneous inequality for every form, including all integer multiples
and the zero form. A bound independent of (h,k) would be impossible
for a nonzero linear form because multiplication scales its value.

If D^2 mu nu -> 0 is subsequently proved for each fixed odd weight,
every sequence with bounded reduced coordinates tends to zero, and
the two chosen basis forms do so. Unbounded reduced coordinates require
the product D^2 mu nu (h_n^2+k_n^2) to tend to zero. No uniformity as
the weight itself tends to infinity is asserted by a fixed-weight limit.

This route optimizes a moment metric on the same integral coefficient
pair lattice. It does not introduce a new rational kernel, discard a gcd,
or infer small cost from rank alone.

## Exact remaining asymptotic target

It suffices to prove D^2 mu nu -> 0 along arbitrarily large eligible
indices. A sufficient fixed-weight rate is

    limsup [2log(D)+log(mu)+log(nu)]/n < 0.

Using the existing analytic bound mu<=poly_s(n)*exp(-A_s*n), where
A_s=log(2397*4^(s-7)), and log(d_n)/n -> 1, the sufficient target becomes

    limsup log(nu)/n < A_s-2s.

This inequality is not proved. It is a new explicitly computable metric
formulation, not a completed substitute for the arithmetic growth proof.
In particular subexponential savings alone cannot repair a strictly
positive limiting exponent in a bound. The full rate must be tracked.

## Reproducible checks

`scripts/moment_metric_reduction.py` constructs M and F exactly, forms G
including the certified infinite-tail diagonal, reduces S, and checks
both primitive bounds independently against Euler--Maclaurin enclosures.
It covers weight 7 at n=6,8,12,20,40,80,160, weight 9 at n=8,12,20,40,
and weights 11,13,15,17,21 at n=2r and n=4r. There are 42 selected forms
and five additional reduced-coordinate checks per matrix, including
zero, multiples, and nonintegral pairs. The first 22 squared bounds
are below one; the additional cases are reported without an assumption
on that threshold. In the expanded run, 40 bounds are below one; the
two at weight 21, n=20, exceed one. Every interval and homogeneous
inequality check passes, including those two larger bounds. The stored data include
the old absolute-profile majorant for the same pair, enabling a direct
comparison without conflating a changed pair with a changed estimate.

At n=160 the initial fixed precision of the independent zeta enclosure
was insufficient after multiplication by the large coefficient pair.
The final script uses order max(96,2n); all interval checks then pass.
No floating-point estimate enters a certificate. The finite examples
are not extrapolated to a uniform rate. These arguments are paper proofs;
this pass adds no Lean formalization or unconditional irrationality claim.
