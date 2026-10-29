# Improve the error budget by recentering the signed prefix

The earlier cofactor-root method bounded a nonzero signed prefix as
part of the approximation error. That discards useful rational data.
The following exact correction reuses the same kernels and adjugate.

Let the primitive cofactor-root form have coefficient pair p0,q0 with
p0!=0, and let F_K be its rational signed prefix. The certified tail is

    p0 zeta(s)+q0=F_K+T_K, |T_K|<=e_K.

The old centre and radius are sigma0=-q0/p0 and
delta0=(|F_K|+e_K)/|p0|, possibly enlarged to ensure positivity.
Instead define

    sigma1=(F_K-q0)/p0, delta1=e_K/|p0|.                     (1)

Then zeta(s)-sigma1=T_K/p0, and therefore

    |zeta(s)-sigma1|<=delta1,
    |sigma1-sigma0|+delta1=(|F_K|+e_K)/|p0|<=delta0.          (2)

Thus the new certified interval is contained in the old one. The
nonzero prefix becomes an exact rational correction rather than an
error term. The cutoff and coefficients of the root form are unchanged.

More generally, for any fixed b>1 the previous doubling procedure can
choose the root-form cutoff with e_K<=b^(-n). Because p0 is a nonzero
integer, |p0|>=1, so delta1<=e_K<=b^(-n). Thus the corrected centres
have a proved uniform accuracy certificate at any prescribed geometric
precision. This does not give the same rate for the selected integer
forms: the denominator of the corrected centre and its convergent gaps
change with the precision and remain part of the arithmetic problem.
The centres and cutoffs in this statement depend on b; it does not
assert all geometric rates for one fixed sequence of centres.

## An improvement that cannot worsen the previous bound

For an integer form q alpha-p and a certified interval with centre c
and radius d>=0, use the exact bound

    B_(p,q)(c,d)=|q c-p|+|q|d.

If |c1-c0|+d1<=d0, the triangle inequality proves

    B_(p,q)(c1,d1)<=B_(p,q)(c0,d0)                          (3)

for every fixed integer pair. Retain the previously selected unimodular
pair as a candidate, and add consecutive convergents of sigma1. Minimize
the common interval bound over this union. The new minimum E1 then obeys

    0<E1<=E0.                                             (4)

The retained pair need not be consecutive convergents of the new centre;
its unit determinant and the exact interval bound are sufficient. A
reciprocal-denominator estimate for new convergents is not silently
applied to that retained pair.

Every candidate pair remains primitive and independent. At least one
associated integer form is nonzero, without an irrationality assumption.
The signed-prefix certificate supplies an exact nonzero interval as
before. No separate gcd or denominator saving is inserted into (3).
The possibly larger denominator of sigma1 is handled by the actual
integer convergents and their explicit error terms.

For epsilon_i,n=-log(E_i,n)/n at n>0, (4) gives the pointwise identity
and inequality

    epsilon1,n-epsilon0,n=log(E0,n/E1,n)/n>=0.               (5)

Consequently every proved uniform decay rate for the old bound is
preserved. A uniform positive extra gain would require an additional
bound on E1/E0; it is not proved by (4) alone.

## Exact finite improvement

The script recentered_cf_root.py verifies ten actual profiles at weights
7,9,11. All ten satisfy the stronger finite inequality E1*8^n<E0,
so their epsilon gain is strictly greater than log8. This inequality
is checked with rational arithmetic, not fitted from logarithms.

At weight seven the directly certified common majorants are below

| n | new rigorous upper bound |
|---|---|
| 6 | 3 * 10^(-14) |
| 8 | 7 * 10^(-27) |
| 12 | 5 * 10^(-37) |
| 16 | 4 * 10^(-49) |
| 20 | 3 * 10^(-77) |

These use the same root-form cutoff precision as the previous method.
There are thirty signed-prefix certificates and twelve rational-target
controls. For the rational target 3/2 the improved common bound stays
at least 1/2, even though interval refinement is valid. The method does
not assume that every real target is irrational.

Four Lean lemmas signed_prefix_recenter_error,
signed_prefix_recenter_radius, integer_recenter_radius_le and
nested_interval_form_majorant verify the exact correction, integer
radius bound and interval comparison. The full factorial-family
and continued-fraction application is the paper argument above.
There is a proved pointwise non-worsening result and a strict finite
improvement; a uniform strict improvement and the all-odd irrationality
endpoint remain unproved.
