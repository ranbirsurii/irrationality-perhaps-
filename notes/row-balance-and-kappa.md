# Row balance is subexponential; the lattice-shape estimate remains

For the actual three-block weight-five family, the row-balance factor
is now proved to satisfy

\[
 \boxed{\lim_{n\to\infty,\ n\text{ even}}\frac{\log R_n}{n}=0.} \tag{1}
\]

The argument is a recurrence theorem with a universal polynomial
certificate for the third block. It uses no finite-index extrapolation.
It also sharpens the primitive-normal upper rate. The discriminant
calculation below gives an unconditional bound on kappa_n, but that
bound is too weak for the irrationality argument. Neither the required
kappa_n rate nor the proposed Gamma_n rate is asserted as proved.

## The third-block polynomial certificate

For a=0,1,2 put

\[
 R_n^{(a)}(t)=(n!)^3
 \frac{\prod_{v=1}^{n-a}(t-v)(t+n+v)}
 {\prod_{j=0}^n(t+j)^5},
 \qquad v_n^{(a)}=\sum_j[t+j]^{-3}R_n^{(a)}.
\]

The last expression means the sum of third-order Laurent coefficients
at the poles -j, not expansion at infinity. We use even n>=2 throughout.
The actual normalized coefficients are

\[
 a_3(n,n)=v_n^{(0)},\quad
 a_3(n,n-1)=n^2v_n^{(1)},\quad
 a_3(n,n-2)=n^2(n-1)^2v_n^{(2)}.                              \tag{2}
\]

The complete certificate for a=2 is
`pade-offset-two-recurrence.json`. It specifies integer polynomials
X(n,t)=sum_(j=0..30)x_j(n)t^j and q_0,...,q_3. Define

\[
 U=t^6(t+2n-a+1),\qquad V=(t-n+a-1)(t+n+6)^6,
\]
\[
 H_\ell=
 \prod_{i=1}^{2\ell}(t-n+a-i)
 \prod_{i=1}^{4\ell}(t+2n-a+i)
 \prod_{i=2\ell+1}^{6}(t+n+i)^6.
\]

The verified identity in Z[n,t] is

\[
 U X(n,t+1)-V X(n,t)=\sum_{\ell=0}^3q_\ell(n)H_\ell(n,t).       \tag{3}
\]

For a=2 the polynomial normalization factor is

\[
 g_2(n)=(n+1)\prod_{i=2}^6(n+i)^3,
\]

and the certificate gives degree-46 integer polynomials P_ell with

\[
 q_\ell(n)\prod_{i=2\ell+1}^6(n+i)^3=g_2(n)P_\ell(n).
\]

Their leading coefficients, in order, are

\[
 (-6060191213313,\ 125910797226792849,\
   253630224853470,\ 8313019497).
\]

For the recurrence interpretation set
B=R_n^(a)/product_(i=1..6)(t+n+i)^6 and G=VXB. The shift ratio gives

\[
 G(t+1)-G(t)=\sum_{\ell=0}^3
 \frac{q_\ell(n)}{\prod_{i=1}^{2\ell}(n+i)^3}R_{n+2\ell}^{(a)}(t).
\]

All poles of G are nonpositive integers and
G(t)=O(t^(-3n-2a-4)). For n>a, R_n^(a)(1)=0. At the remaining
endpoint n=a=2, V(1)=0. Thus G(1)=0 throughout the range. Summing
third-order pole coefficients cancels along the finite pole orbits of
G(t+1)-G(t), and multiplying by the displayed normalization gives

\[
 \sum_{\ell=0}^3P_\ell(n)v_{n+2\ell}^{(2)}=0.                 \tag{4}
\]

The verifier `scripts/verify_row_balance.py` expands every coefficient
of (3) and verifies the normalization identity, using only integer
arithmetic. It checks the existing a=0,1 certificates in the same
way. It evaluates no family indices. Optional symbolic discovery is
reproducible with `scripts/generate_sign_recurrences.py --offset 2`.

## A common dominant rate for the first two coefficients

For all three a, the companion matrices for (4) or the existing
recurrences have the same limit

\[
 A=\begin{pmatrix}0&1&0\\0&0&1\\729&-15146217&-30510\end{pmatrix}.
\]

After alternating signs with the step n->n+2, the characteristic
polynomial is

\[
 f(z)=z^3-30510z^2+15146217z+729.
\]

Exact signs at the interval endpoints show one root in each of
(-1,0), (1,1000), (30005,30006). These three intervals exhaust the
roots and establish distinct absolute values. Denote the largest
positive root by rho.

The classical Poincare-Perron theorem says that a solution to a scalar
recurrence whose coefficients converge and whose limiting roots have
distinct absolute values either vanishes eventually or has successive
ratio tending to one of those roots. We use Theorem 2(i) of
[Borcea, Friedland and Shapiro, Parametric Poincare-Perron theorem
with applications](https://arxiv.org/pdf/0909.1216).
The recurrence coefficients are rational functions of n and their
leading denominator polynomials are nonzero, so they are defined
for every sufficiently large n. The theorem applies after discarding
at most a finite initial segment.

For a=0,1 the proved positivity cones give
-v_(n+2)^(a)/v_n^(a)>=1000 at every even n>=2. Hence their alternating
ratio limits must equal rho, since the other two roots have modulus
less than 1000. It follows by taking logarithms and Cesaro means that

\[
 \lim\frac{\log|v_n^{(a)}|}{n}=\ell:=\tfrac12\log\rho,
                  \qquad a=0,1.
\]

For a=2 the same theorem implies

\[
 \limsup\frac{\log(1+|v_n^{(2)}|)}{n}\le\ell,
\]

including the possibility of eventual vanishing. No global sign for
the third coefficient is needed. Polynomial scaling in (2) does not
alter these exponential rates.

Let b_i=a_3(n,n-i), P=sum_i max(b_i,0) and T=sum_i max(-b_i,0).
The adjacent-sign theorem gives b_0*b_1<0. Thus

\[
 1\le R_n=\frac{\max(P,T)}{\min(P,T)}
 \le\frac{\sum_i|b_i|}{\min(|b_0|,|b_1|)}.
\]

The logarithms of both numerator and denominator, divided by n,
tend to ell. This proves (1). Clearing all coefficients by d_n^5
does not change R_n. In particular log(1+2R_n)/n tends to zero.
This proves exactly the needed zero exponential contribution; a
polynomial bound R_n=O(n^c) is not asserted from ratio convergence alone.

## A sharper unconditional primitive-normal bound

The same argument proves log(norm(x_n))/n -> 5+ell. Combining it
with the previously proved lower-column divisor gives

\[
 \limsup\frac{\log H_n}{n}\le5+\ell-c_g,
 \quad H_n=\|x_n/g_n\|_2,\quad
 c_g=3+\frac\pi{4\sqrt3}+\frac34\log3.
\]

Since 30005<rho<30006, the right side is less than 5.877168.
This improves the earlier coefficient-magnitude upper bound 6.097870.

## Controlling kappa by the actual discriminant

Take a Gauss-reduced basis a,b of the saturated cancellation lattice.
Write A=a*a, B=a*b, C=b*b, so 1<=A<=C and abs(B)<=A/2. The exact
cross-product identity gives

\[
 AC-B^2=H_n^2,\qquad
 \Delta_n=(2B)^2-4AC=-4H_n^2.
\]

Here Delta_n is the discriminant of the binary quadratic form. It
has not been identified with the discriminant of a fixed number field
generated by the periods. Directly from these identities,

\[
 \kappa_n^2=\frac CA
        =\frac{H_n^2}{A^2}+\left(\frac BA\right)^2
        \le H_n^2+\frac14.
\]

Therefore the following bound is proved unconditionally:

\[
 \boxed{\kappa_n\le\sqrt{H_n^2+\tfrac14},\qquad
 \limsup\frac{\log\kappa_n}{n}<5.877168.}                      \tag{5}
\]

It is not the required small rate. More precisely, writing theta_n
for the angle of the reduced basis and lambda_(1,n)=sqrt(A), one has

\[
 \log\kappa_n=
 \log H_n-2\log\lambda_{1,n}-\log\sin\theta_n,
 \qquad \sqrt3/2\le\sin\theta_n\le1.                         \tag{6}
\]

Thus the unresolved shape estimate is a lower bound for the shortest
nonzero integer relation among the actual three coefficients, relative
to sqrt(H_n). A recurrence theorem for a fixed scalar solution does
not control all such integer relations whose coefficients vary with n.
No bound strong enough for that task has been established here.

## The improved conditional budget and its two dependencies

Let c_Gamma=3/2+(3/2)log(3), the proposed but still unproved image
content rate. If liminf log(Gamma_n)/n>=c_Gamma were proved, then
the positive-rounding construction and (1) would give

\[
 \limsup\frac{\log K_n^{\rm new}}n
 \le c_{\rm new}+\tfrac12\limsup\frac{\log\kappa_n}n,
\]

where

\[
 c_{\rm new}=5+\tfrac12(5+\ell-c_g)-c_\Gamma<4.790666.
\]

Consequently the rate bound

\[
 \limsup\frac{\log\kappa_n}n\le0.30                           \tag{7}
\]

would suffice, together with that content estimate, since
4.790666+0.15<log(140). The already proved analytic comparison
C_0*(n+1)^12*K_n/140^n would then tend to zero. The constant enclosures
are in `row-balance-rate-budget.json`; they enclose constants, not
sampled indices. Statement (7) is not proved by (5).

There is also a direct joint target that avoids prescribing separate
rates for kappa_n and Gamma_n. Before bounding the longer basis
length by the area, positive rounding gives

\[
 K_n^{\rm new}\le3d_n^5(1+2R_n)\lambda_{2,n}/\Gamma_n.
\]

Since (1) is proved, it is sufficient to establish

\[
 \boxed{\liminf\frac{\log\Gamma_n-\log\lambda_{2,n}}n
                         >5-\log140.}                        \tag{8}
\]

For example Gamma_n>=exp(0.06*n)*lambda_(2,n) at arbitrarily large
even indices would suffice: the cost upper rate along those indices
would be at most 4.94, strictly below log(140). This follows from the
proved comparison, with no assumption about kappa_n on that subsequence.
It is a possible replacement for the two separate arithmetic estimates,
not a proved joint bound. Neither (7) with the content estimate nor
(8) has been established.

Gamma_n is a sufficient auxiliary content, not a logically mandatory
symbol in every possible proof. It could be replaced by a direct bound
on the selected h_n/M_n. Removing it without a replacement would,
even if kappa_n were subexponential, leave only an upper cost rate
5+(5+ell-c_g)/2, greater than 7.9385. This bound does not imply
vanishing. It is not a proof that the actual forms fail to vanish.

For the proposed Dwork route, higher-order Cartier congruences have
explicit hypotheses. In
[Beukers and Vlasenko, Dwork crystals III](https://arxiv.org/pdf/2105.14841),
Theorem 4.2 assumes maximality on the indicated filtration pieces,
and Corollary 5.9 uses the higher Hasse-Witt conditions. An integral
identification with the present selected minors, together with these
conditions and the division by g_n, has not been constructed. No
automatic higher-order divisibility is inferred from the word Frobenius.

The row-balance theorem (1), its polynomial certificate and the sharper
height bound are proved on paper, with the universal identities checked
independently. The winning shape bound (7) and the content rate remain
unproved. These results are not a complete irrationality theorem or
a completed Lean formalization. No Lean or TeX compilation was performed.
