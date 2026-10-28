# A uniform recurrence in the block length

This gives a simpler all-index algebraic description of the positive
family used in the three-block search. It does not prove the required
limiting lattice-cost estimate. No new Lean or TeX compilation was done.

Fix an even n>=4 and let V_m be the rational period-coordinate vector
of the normalized kernel T_(n,m), in the order (zeta(3),zeta(5),constant).
For 0<=m<=n-3, set c_i=(m+i)(n+m+i), i=1,2,3, and

\[
 a_1=n^4(6m+6-n),\quad a_2=n^2(9m+9-5n),\quad a_3=2m+2-5n.
\]

Define

\[
 q_0=(m+1)^6(n+2m+2),
\]
\[
 q_1=a_1+a_2(c_1+c_2)+a_3(c_1^2+c_1c_2+c_2^2),
 \quad q_2=a_2+a_3(c_1+c_2+c_3),\quad q_3=a_3.
\]

The exact block recurrence is

\[
 \boxed{\sum_{\ell=0}^3 q_\ell
       \left(\prod_{i=1}^{\ell}(m+i)^2\right)V_{m+\ell}=0.}
 \tag{1}
\]

In particular, all its coefficients are explicit polynomials in n,m;
the large n-index recurrence coefficients are not needed for (1).

## Polynomial certificate and boundary proof

Put u=t(t+n), U=t^6(t+n+m+1) and W=(t-m-1)(t+n)^6. Direct expansion gives

\[
 U-W=(m+1)n^6+a_1u+a_2u^2+a_3u^3.
\]

Expanding this cubic in its Newton basis at c_1,c_2,c_3 yields

\[
 U-W=\sum_{\ell=0}^3q_\ell
                  \prod_{i=1}^{\ell}(u-c_i).
 \tag{2}
\]

For example q_0 is its value at u=c_1; evaluating at t=m+1 makes
W=0 and gives exactly the stated q_0. The other displayed formulas
are the ordinary divided differences of that cubic.

The exact term ratio is

\[
 \frac{T_{n,m}(t+1)}{T_{n,m}(t)}=
 \frac{t^6(t+n+m+1)}{(t-m)(t+n+1)^6}.
\]

Consequently G(t)=W(t)*T_(n,m)(t) satisfies

\[
 G(t+1)-G(t)=(U-W)T_{n,m}(t)
  =\sum_{\ell=0}^3q_\ell
        \left(\prod_{i=1}^{\ell}(m+i)^2\right)T_{n,m+\ell}(t).
\]

At t=1 its lower boundary vanishes: T_(n,m)(1)=0 when m>=1,
while W(1)=0 when m=0. Its degree at infinity is 2m-5n+2<=-3n-4,
so its upper boundary also vanishes. Applying the Laurent coefficient
sum functionals and then the rational harmonic boundary formula, as
in the adjacent-family certificate, gives (1) without assuming any
linear independence of zeta values. It also gives the same recurrence
for the actual positive sums.

The standard-library checker expands (2) as an identity in Z[n,m,t].
It separately checks fourteen exact three-coordinate recurrences as
implementation checks; the polynomial and boundary arguments prove
the general statement.

## Uniform signs and the complete positive cone

On the whole range 0<=m<=n-3,

\[
 q_0>0,\qquad q_1<0,\qquad q_2<0,\qquad q_3<0.
\]

For a coefficientwise proof substitute n=m+3+r. Every coefficient of
q_0 in m,r is positive, and every nonzero coefficient of each of
q_1,q_2,q_3 is negative; their constant coefficients are strictly
negative. The checker verifies these complete finite expansions, so
the conclusion holds for all m,r>=0, without finite-index extrapolation.

Solving (1) for V_m therefore expresses it as a strictly positive
rational combination of V_(m+1),V_(m+2),V_(m+3). Descending induction
shows

\[
 \boxed{\operatorname{cone}_{\mathbb Q_{\ge0}}\{V_0,\ldots,V_n\}
  =\operatorname{cone}_{\mathbb Q_{\ge0}}\{V_{n-2},V_{n-1},V_n\}.}
\]

For n=2 this statement is immediate. Thus the three blocks capture the
entire positive rational cone of these lengths. Intersecting that cone
with the lower-period cancellation plane preserves the equality.
Clearing rational weights and primitive normalization then preserves
the set of obtainable primitive coefficient pairs, up to the common
positive scaling.

The rational coefficients accumulated over many reductions have their
own denominator cost. This cone equality does not declare those
reductions arithmetically free or replace the cost analysis in the
three-block note.

## A Casoratian and the remaining arithmetic

For W_m=det(V_m,V_(m+1),V_(m+2)), the companion determinant gives

\[
 W_{m+1}=
 \frac{(m+1)^4(n+2m+2)}
 {(5n-2m-2)(m+2)^2(m+3)^2}\,W_m.
\]

This controls the full determinant, with its normalization explicit.
It does not identify a selected-minor gcd with that determinant or
with a real spectral rate. The outstanding estimate still concerns
the integral cancellation lattice and its image content Gamma_n.

## Quantified finite decay and a sufficient uniform target

The exact three-block certificates prove

\[
 0<L_n<e^{-n/5}
\]

at the ten audited indices 4,8,12,20,40,80,160,320,640,1280.
This follows by comparing the rational upper endpoints for
log(upper bound)/n with -1/5. The word "audited" is essential: this
is a finite set, not an all-index decay theorem.

At n=1280 the separately recorded lattice quantities have rates

\[
 \log J_n/n\approx0.002062,\quad
 \log Q_n/n\approx2.925301,\quad
 \log\Gamma_n/n\approx3.117103.
\]

The exact ratio J_n Q_n/Gamma_n has logarithmic rate near -0.189740
at this index. Rational enclosures are recorded in the audit data.
For example, a sufficient all-index statement, stronger than necessary,
would be

\[
 \Gamma_n\ge e^{n/10}J_nQ_n\quad\text{eventually}.
 \tag{3}
\]

The established denominator and analytic limits would then imply,
eventually,

\[
 d_n^5\le e^{5.01n},\qquad
 \max_i\mathcal A_{n,n-i}\le e^{-4.9707n},
\]

and hence

\[
 0<L_n\le e^{(5.01-0.1-4.9707)n}
          =e^{-0.0607n}\longrightarrow0.
\]

An unbounded subsequence satisfying the corresponding estimates would
also suffice. The present certificates verify the saving in (3) at
320,640,1280, but do not prove infinitely many instances or an eventual
bound. Stating (3) as a hypothesis does not close the irrationality proof.
The uniform recurrence and cone reduction above are proved; this
additional arithmetic growth statement is not.
