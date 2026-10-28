# Arithmetic growth and the proposed Connes-Consani comparison

The weight-five adjacent sign and nonvanishing result is now proved in
`global-coefficient-sign.md`. This note states the arithmetic estimate
still required and separates it from geometric reinterpretation.

## The exact comparison that would finish smallness

Let integer weights w_(n,j) cancel the lower period, let
M_n=sum_j |w_(n,j)|, and put

\[
 d_n^5\sum_jw_{n,j}\mathcal A_{n,n-j}=A_n\zeta(5)+B_n,
 \qquad h_n=\gcd(|A_n|,|B_n|).
\]

The exact multiplier relative to the rational form with sum of absolute
weights one is

\[
 K_n=\frac{d_n^5M_n}{h_n}.
\]

The analytic rate lambda_5 lies in (-4.970794,-4.970793).
Consequently, a sufficient estimate is

\[
 \limsup_{n\to\infty,\ n\text{ even}}
 \frac{5\log d_n+\log M_n-\log h_n}{n}<-\lambda_5.
\]

Using the classical prime number theorem log(d_n)/n -> 1, this becomes

\[
 \boxed{\liminf_{n\to\infty,\ n\text{ even}}
   \frac{\log h_n-\log M_n}{n}>5+\lambda_5.}
\]

The right side is between 0.029206 and 0.029207. For example, a proved
lower bound h_n/M_n >= exp((0.029207+epsilon)*n), eventually with a fixed
epsilon>0, would suffice. This is a statement about the complete output
gcd relative to the cancellation weights. A saving in a basis denominator
alone does not establish it. No such lower bound is proved here.

Rescaling integer weights multiplies h_n and M_n equally. Overclearing
coefficient denominators likewise multiplies the clearing factor and
the full gcd equally. Neither changes the primitive form. Those
invariances have already been verified in the Lean development.

## What the cited geometric constructions supply

The 2026 preprint [Connes-Consani, The Absolute Twistor Line and the
Geometry of the compactified Spec Z](https://arxiv.org/abs/2609.00299)
constructs an archimedean twistor geometry and describes odd Frobenius
actions, Adams operations and conjugation of real Hodge structures,
particularly in Sections 5-7. Its Theorem 5.1 identifies the induced
twistor real structure. It does not identify the present coefficient
lattices or state the boxed gcd-to-weight estimate.

The earlier [cyclic-homology theorem](https://arxiv.org/abs/1211.4239)
expresses archimedean local L-factors through regularized determinants.
That theorem is not a bound on this finite-prime coefficient content.
These are scoped descriptions of the statements examined, not an
assertion that their techniques could never help.

A usable arithmetic bridge would need to construct the particular
coefficient lattices and comparison maps, identify their integral
indices with divisibility of A_n and B_n, and quantify those indices
relative to M_n. A weight shift or a rational common rescaling without
that comparison does not imply the required divisibility.

There is also a separate analytic requirement when applying a weight
projector. Smallness of one period pairing does not bound a projected
pairing automatically. For x,y>0 consider the linear functional
ell(a,b)=x*a+y*b and the projector P(a,b)=(0,b). At (a,b)=(y,-x),
ell(a,b)=0 but ell(P(a,b))=-x*y!=0. Hence there is no universal finite
constant C satisfying |ell(Pv)|<=C*|ell(v)| for all real vectors v.
A family-specific bound on the projected periods is needed in addition
to the existence of the operation. This does not rule out such a bound
for constructed geometric classes; it identifies what must be proved.

## What the new recurrence says

The leading coefficient ratios of both certified third-order recurrences
are exactly

\[
 (P_0/P_3,P_1/P_3,P_2/P_3)\longrightarrow
                  (-729,15146217,30510).
\]

The sign-normalized limiting characteristic polynomial is therefore

\[
 z^3-30510z^2+15146217z+729.
\]

This is an exact algebraic calculation from the supplied coefficient
lists. It is useful for subsequent analytic and recurrence analysis,
but it does not determine the p-adic gcd h_n or prove its ratio to M_n
has the required limiting growth. No arithmetic gain is inferred merely
from the characteristic polynomial or from a geometric twist.
