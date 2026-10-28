# Local jet conditions and a constructive positive-weight bound

The two arguments below are exact and apply at arbitrary indices. The
first writes the necessary local lifting conditions without assuming
that Mahler interpolation supplies divisibility. The second constructs
positive integer weights and eliminates a separate search-radius factor
from their cost bound. The winning local congruences and lattice-shape
rate are not proved here. No finite-index extrapolation is used.

## Exact finite-difference form of the local minors

For the three actual scaled coordinate rows at an eligible prime p,
write

\[
 V_i=(X_i,Y_i,Z_i)
   =(p^2a_3(n,n-i),a_5(n,n-i),p^5b(n,n-i)),\quad i=0,1,2.
\]

All entries are in the local ring Z_(p). Define

\[
 U=V_0,\qquad D=V_1-V_0,\qquad E=V_2-2V_1+V_0.
\]

The polynomial U+sD+binom(s,2)E interpolates the three rows at
s=0,1,2. This is a finite Newton expansion; it needs no unproved
continuous interpolation of the factorial family in n. For either
selected coordinate pair, write wedge for its two-by-two determinant.
Bilinearity gives the exact identities

\[
 V_0\wedge V_1=U\wedge D,
\]
\[
 V_0\wedge V_2=2U\wedge D+U\wedge E,
\]
\[
 V_1\wedge V_2=U\wedge D+U\wedge E+D\wedge E.                 \tag{1}
\]

The transformation from the three wedges on the right to the original
three minors has integer determinant one. Thus, for any integer e>=0,
all original selected minors lie in p^e*Z_(p) if and only if all
three finite-difference wedges do. The same transformation on cleared
integer rows preserves their selected-minor gcd and the gcd g_n of
their distinguished column. This is an equality of contents, not a
gain in their valuations.

For a precise first lift, put n=pq+r, A_i=a_5(r,r-i) and

\[
 Q=(a_3(q,q),a_5(q,q),b(q,q)),\qquad
 W_i=(V_i-A_iQ)/p\in\mathbb Z_{(p)}^3.
\]

The existing first-order kernel congruence proves the integrality of
W_i. Expanding the determinant yields

\[
 \boxed{V_i\wedge V_j
 =p\,Q\wedge(A_iW_j-A_jW_i)+p^2W_i\wedge W_j.}                \tag{2}
\]

Consequently the second-order lifting condition is exactly

\[
 Q\wedge(A_iW_j-A_jW_i)=0\pmod p.                             \tag{3}
\]

It does not follow merely from the integrality of W_i. At higher orders
the right-hand side of (2), divided by p, must itself be shown divisible
by the remaining power. This is where a valid product expansion of
the rational kernel would have to enter.

Let t=v_p(g_n). Since the cleared coordinates are
(x_i,y_i,z_i)=(p^3uX_i,p^5uY_i,uZ_i), with u a local unit, the target
v_p(Gamma_n)>=2+c_(n,p) requires, for every pair i<j,

\[
 v_p(X_iZ_j-X_jZ_i)\ge t-1+c_{n,p},
\]
\[
 v_p(X_iY_j-X_jY_i)\ge t-6+c_{n,p}.                            \tag{4}
\]

Negative right sides impose no additional condition, since the scaled
minors are integral. Formula (4), with the actual t, retains the loss
from division by g_n. Equations (1)-(2) give exact algebraic expressions
for those targets. Equations (3)-(4) have not been established for
all the required kernel parameters. There is currently no Lean proof
of those family-specific higher-order congruences.

Mahler's theorem gives an expansion for a continuous function on Z_p;
it does not supply the divisibility of its initial coefficients. See
[Conrad, Mahler expansions](https://kconrad.math.uconn.edu/blurbs/gradnumthy/mahlerexpansions.pdf).
The local-global supercongruence theorem of
[Pan, Tauraso and Wang](https://arxiv.org/abs/1909.08183) requires
regularity and congruences on suitable hyperplanes. No verified
parameter identification or such hyperplane congruences for (4) are
being assumed in this note.

## Positive weights by rounding a point in the cone

Here is a constructive bound with no search-radius parameter. Let
x be any nonzero integer row with both positive and negative entries.
Let a,b be an integer basis of its full integer kernel, ordered so that
lambda_1=norm(a)<=lambda_2=norm(b). Define

\[
 P=\sum_i\max(x_i,0),\qquad T=\sum_i\max(-x_i,0),\qquad
 R=\frac{\max(P,T)}{\min(P,T)}\ge1.
\]

There is a primitive strictly positive integer vector w in the kernel
such that

\[
 \boxed{\|w\|_1\le3(1+2R)\lambda_2.}                          \tag{5}
\]

Proof. Set v_i=T when x_i>=0 and v_i=P when x_i<0. Then
x*v=PT-TP=0 and every v_i is positive. Write m=min_i(v_i)=min(P,T)
and

\[
 \rho=\frac12\max_i(|a_i|+|b_i|)>0.
\]

Express v=alpha*a+beta*b in the kernel basis. These coordinates are
integers by saturation. Round each of (2*rho/m)*alpha and
(2*rho/m)*beta to the nearest integer, obtaining s,t, and set
w'=s*a+t*b. The rounding error in each ambient coordinate is at
most rho. Hence

\[
 w'_i\ge(2\rho/m)v_i-\rho\ge\rho>0.
\]

Moreover

\[
 \sum_iw'_i\le(2\rho/m)\sum_iv_i+3\rho
                   \le3\rho(1+2R).
\]

Since rho<=norm(a)/2+norm(b)/2<=lambda_2, this proves the bound
for w'. Dividing its coordinates by their gcd preserves strict
positivity, integrality and cancellation, and can only decrease the
mass. This proves (5).

The construction uses exact rational arithmetic. To compute alpha,beta,
let A=a*a, B=a*b, C=b*b, u=a*v, z=b*v. Solving the Gram system gives

\[
 \alpha=(Cu-Bz)/(AC-B^2),\qquad
 \beta=(Az-Bu)/(AC-B^2).
\]

The denominator is positive because a,b are independent. This supplies
an explicit implementation, not just an existence argument based on
ellipsoid volume. The function `positive_rounding_weights` in
`scripts/three_block_lattice_search.py` performs these operations and
adds the resulting candidate to the existing selection. The finite
records from earlier versions have not been regenerated or relabeled.

## Applying the bound to the actual primitive forms

The adjacent-sign theorem ensures that the actual x_n has both signs,
so (5) applies at every even n>=2. The new candidate is strictly
positive, and the existing positivity and denominator results apply
to its combined form. Its output coefficient content is at least
Gamma_n, as for any integer kernel vector.

Put H_n=norm(x_n/g_n) and kappa_n=lambda_(2,n)/lambda_(1,n). For a
Gauss-reduced basis, the Gram determinant and its angle give

\[
 \lambda_{2,n}^2\le\frac2{\sqrt3}\kappa_n H_n.
\]

Therefore the rounding candidate, and any candidate selected with
no greater primitive cost, satisfies the all-index bound

\[
 \boxed{K_n^{\rm new}\le
 \frac{3d_n^5(1+2R_n)}{\Gamma_n}
              \sqrt{\frac2{\sqrt3}\kappa_n H_n}.}              \tag{6}
\]

This removes J_n from the sufficient budget. It does not prove that
the remaining row-balance and shape factors are subexponential.
If the previously proposed content rate for Gamma_n were proved,
the exact sufficient remaining condition would be

\[
 \limsup_{n\to\infty,\ n\text{ even}}
 \frac{\log(1+2R_n)+\tfrac12\log\kappa_n}{n}
                         <\log140-c_*,
\]

with c_* as defined in the quotient-prime-loss note. The Gram
determinant alone controls the product of the basis lengths, not
their ratio, so this condition is not supplied by (5)-(6).

The derived identities and the positive rounding bound are proved
above. The family-specific congruences (4) and the winning rate of
the remaining factors in (6) are still unproved. The irrationality
conclusion and a complete Lean formalization do not follow yet.
No finite-index runs or Lean/TeX compilation were performed here.
