# A cancellation-preserving certificate for adjugate forms

This applies the established signed-prefix method to the adjugate root
construction. It does not change the coefficient family or assume that
the resulting forms already decay.

Fix s=2r+1>=7, even n>=2r, m0=n-r. For the existing block m=n-j,
the exact quadratic-factor identity gives

    T_(s,n,m)(t)=T_(s,n,m0)(t) R_m(t(t+n)),
    R_m(u)=(m0!/m!)^2 product_(v=m0+1..m)(u-v(n+v)).          (1)

The identity quadratic_pair_factor and normalized kernel length shift
are already verified in Lean. For the integer adjugate vector
w=pU+qV with coprime p,q and Delta=det B!=0, define

    H_n(u)=sum_j (D/Delta) w_j R_(n-j)(u)=sum_(ell=0..r)h_ell u^ell.

Then the exact normalized period identity is

    L_n=p zeta(s)+q
       =sum_(t=m0+1..infinity) T_(s,n,m0)(t) H_n(t(t+n)).    (2)

The earlier start of the base sum introduces no unwanted terms, since
the factors in R_m vanish at each integer m0<t<=m. The normalization
has already been included in H_n; neither D nor Gamma is charged a
second time. Keep the finite prefix signed before taking an absolute
value.

## Explicit rational tail

For an integer K>=max(1,m0+1), put

    alpha=s(n+1)-2n>1,
    C_K=(n!)^s/(m0!)^2 * (1+(n+m0)/K)^m0,
    V_K=sum_(ell=0..r)|h_ell|(1+n/K)^ell K^(-2(r-ell)),
    e_K=C_K V_K K^(1-alpha)/(alpha-1).                       (3)

For t>K the kernel numerator is bounded by
t^(2m0)(1+(n+m0)/K)^m0 and its denominator below by
t^(s(n+1)). Also t(t+n)<=t^2(1+n/K), so

    |H_n(t(t+n))|<=V_K t^(2r).

Therefore the absolute tail is at most C_K V_K sum_(t>K)t^(-alpha),
and the integral comparison bounds this by e_K. All quantities in
(3) are rational. With

    F_K=sum_(t=m0+1..K) T_(s,n,m0)(t) H_n(t(t+n)),
    R_K=|F_K|+e_K,

we have the rigorous two-sided certificate

    |L_n|<=R_K<=|L_n|+2e_K.                                (4)

The first inequality is the triangle inequality; the second uses
|F_K|<=|L_n|+|F_K-L_n|. Lean verifies this sharpness implication in
signed_prefix_certificate_sharp. The factorial kernel identification
and analytic tail argument here are paper proofs.

## Arbitrarily accurate evaluation without a new height penalty

At fixed n and chosen p,q, the factors C_K and V_K are bounded for
K>=1, and alpha>1. Consequently e_K->0. Starting at K=n+1 and
doubling K terminates for any prescribed positive rational tolerance.
Choosing tolerance 4^(-n) gives, at every index,

    |L_n|<=R_n<=|L_n|+2*4^(-n).                            (5)

The cutoff changes only how the form is bounded, not its integer
coefficients or primitive height. Thus the certificate introduces no
positive asymptotic floor and preserves any exponential decay of the
actual forms, up to the chosen exponentially small evaluation error.
It does not prove that the selected integer pairs produce that decay.
For any chosen sequence of primitive pairs, (5) proves the equivalence
R_n->0 if and only if |p_n zeta(s)+q_n|->0. This is a faithful
certificate, not a proof that either limit is zero.

The exact script checks eight certificates at weights 7,9, using the
fixed pair (-1,1) and one primitive cofactor-root pair per profile.
Independent Euler-Maclaurin zeta enclosures lie inside every signed
prefix/tail interval. The fixed pair gives the constant |1-zeta(s)|,
and the unmodified root choices give large forms in these finite cases.
Neither is evidence for an all-index decaying pair selection.

The remaining arithmetic approximation problem is the original one:
choose a suitably controlled nonzero primitive form, or an independent
pair of them, with a proved decaying rate. Formula (5) makes evaluation
faithful to such a choice; it does not supply it or conclude irrationality.
