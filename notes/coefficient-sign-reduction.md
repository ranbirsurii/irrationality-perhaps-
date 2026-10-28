# Exact extraction of the weight-five lower-period coefficient

This note takes the sign direction first. It proves a uniform local
amplitude bound and gives the exact finite sum and coefficient contours
for the global coefficient. The global adjacent-sign theorem is now proved
by the separate [recurrence argument](global-coefficient-sign.md). A winning
primitive arithmetic bound remains unproved.

## The actual coefficient and its contours

Let n>=2 be even, 0<=m<=n, and use the normalized kernel

\[
 T_{n,m}(t)=\frac{(n!)^5}{(m!)^2}
 \frac{\prod_{v=1}^m(t-v)(t+n+v)}{\prod_{h=0}^n(t+h)^5}
   =\sum_{j=0}^n\sum_{q=1}^5\frac{c_{j,q}}{(t+j)^q}.
\]

The coefficient of zeta(3) in its summed period is
alpha_(n,m)=sum_j c_(j,3). For any fixed 0<delta<1, Cauchy's coefficient
formula gives the exact contour representation

\[
 \alpha_{n,m}=\frac{1}{2\pi i}\sum_{j=0}^n
           \oint_{|z|=\delta}z^2T_{n,m}(-j+z)\,dz.
\]

All circles are positively oriented. The quantity z^5*T(-j+z) is
holomorphic and nonzero at zero, and its coefficient of z^2 is c_(j,3).
This is a constructed coefficient-contour formula. No single Mellin-Barnes
integral with a proved combined-saddle phase shift is asserted.

Define

\[
 B_{n,m,j}=\binom nj^5\binom{j+m}{m}\binom{n-j+m}{m}>0,
\]

\[
 U_{n,m,j}=H_{n-j+m}-H_{j+m}+6(H_j-H_{n-j}),
\]

\[
 V_{n,m,j}=6\bigl(H_j^{(2)}+H_{n-j}^{(2)}\bigr)
             -H_{j+m}^{(2)}-H_{n-j+m}^{(2)},\qquad
 E_{n,m,j}=\frac{U_{n,m,j}^2+V_{n,m,j}}2.
\]

Then the exact finite expression is

\[
 \boxed{c_{j,3}=(-1)^{m+j}B_{n,m,j}E_{n,m,j},\qquad
 \alpha_{n,m}=(-1)^m\sum_{j=0}^n(-1)^j B_{n,m,j}E_{n,m,j}.}
\]

For completeness, set g_j(z)=z^5*T(-j+z). The already derived leading
coefficient is g_j(0)=(-1)^(m+j)*B_(n,m,j). Logarithmic differentiation
of its numerator factors and its regular denominator factors gives

\[
 \frac{g_j'(0)}{g_j(0)}
 =\sum_{v=1}^m\left(-\frac1{j+v}+\frac1{n-j+v}\right)
       -5\sum_{h\ne j}\frac1{h-j}=U_{n,m,j},
\]

\[
 \left(\frac{g_j'}{g_j}\right)'(0)
 =-\sum_{v=1}^m\left(\frac1{(j+v)^2}+\frac1{(n-j+v)^2}\right)
       +5\sum_{h\ne j}\frac1{(h-j)^2}=V_{n,m,j}.
\]

Thus g_j''(0)/2=g_j(0)*(U^2+V)/2, proving the boxed expression.
No global choice of a logarithm is needed: g_j'/g_j is a rational
logarithmic derivative on the neighborhood where g_j is nonzero.

## A uniform local sign theorem

For all n>0, m<=n and j<=n,

\[
 V_{n,m,j}\ge3\bigl(H_j^{(2)}+H_{n-j}^{(2)}\bigr),\qquad
 \boxed{E_{n,m,j}\ge\frac32 H_n^{(2)}>0.}
\]

Here is an elementary proof valid at every index. Write
A=H_j^(2), B=H_(n-j)^(2), C=H_m^(2).
Positive decreasing summands give

\[
 H_{a+b}^{(2)}\le H_a^{(2)}+H_b^{(2)},\qquad
 C\le H_n^{(2)}\le A+B.
\]

Consequently

\[
 V\ge6(A+B)-(A+C)-(B+C)
       =5(A+B)-2C\ge3(A+B).
\]

Since U^2>=0 and H_n^(2)>0, both boxed inequalities follow. In particular,
every local third-order coefficient has the exact sign (-1)^(m+j).

`OddZeta/PadeCoefficientSign.lean` proves monotonicity and subadditivity
of the harmonic sums, the curvature bound, positivity and the uniform
lower bound for E, and the signed positivity of the displayed algebraic
coefficient expression. Its identification with the Laurent coefficient
is proved above on paper, not formalized as an analytic residue theorem.

## The remaining global sign is explicit

One sufficient target for n even is now

\[
 (-1)^{n/2}\sum_{j=0}^n(-1)^j B_{n,m,j}E_{n,m,j}>0
       \quad\text{for }m=n,n-1.
\]

It implies alpha_(n,n)*alpha_(n,n-1)<0. The uniform local sign theorem
alone does not prove this alternating-sum inequality. The separate recurrence
argument now proves it for m=n,n-1. In general, even a
symmetric sequence of strictly positive amplitudes can have the wrong
alternating-sum sign: at n=2, amplitudes (1,1,1) give sum 1, while the
proposed middle-parity sign would require a negative sum. The actual
binomial-harmonic amplitudes have additional structure; that structure
must enter a global proof.

The block shift changes not only (-1)^m, but also every B_(n,m,j) and
E_(n,m,j). Therefore the explicit local factor (-1)^m cannot be promoted
to an established global Stokes factor exp(i*pi).

The single-to-multiple-sum transformations in
[Krattenthaler and Rivoal](https://doi.org/10.1090/MEMO/0875) are a
classical candidate for replacing an alternating coefficient expression
by a manifestly signed one. No parameter matching or transformation
proving the last displayed inequality has been completed here; their
denominator theorem is not invoked as a proof of this sign claim.

## Scope of the proposed geometric and arithmetic shortcuts

The proved block recurrence is an identity in m with n fixed. Applying
Birkhoff-Trjitzinsky theory to a system evolving in n requires that
system, its asymptotic hypotheses, and the connection coefficient for
the selected solution. They have not been supplied by relabeling the
block shift as a Stokes move.

The roots of the numerator of one fixed rational kernel do not define
the indicial equation of an unspecified flat connection. A rational
function itself is single-valued around its poles. A nontrivial period
connection and a comparison to these coefficients would be additional
constructions.

For arithmetic growth, the actual multiplier remains

\[
 K_n=\frac{d_n^5\sum_j|w_{n,j}|}{h_n},
\]

with the complete coefficient gcd h_n. A proposed reduction of a basis
denominator alone does not control this quantity. No Robba-ring
Frobenius module, trace identity, or valuation theorem establishing
the asserted rates 4.85 or 4.91 is constructed here. The numerical
difference 5-4.970793860... is a deficit before additional savings,
not a proved positive safety margin.

## Verification

The formula was checked independently against the existing Laurent
Taylor calculation for every m<=n at n=2,4,6,8,12,20: 58 kernels and
774 local third-order coefficients. All comparisons are exact rational
equalities. The adjacent global signs are negative for each of the
40 even indices from 2 through 80, using the new exact finite sum.
Those 40 cases remain finite evidence, not an all-index sign theorem.

```text
python scripts/pade_coefficient_sign.py --output pade-coefficient-sign.json
lake build
lake env lean scripts/AuditCoefficientSign.lean
```

The seven new foundation reports use only standard Lean foundations.
The complete project entry point compiled with the new module imported.
No proof placeholders, project axioms, percent characters or hidden
formatting characters were added to the new Lean source.
