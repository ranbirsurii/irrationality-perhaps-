# Determinantal arithmetic budget and the proposed completion

The proposed argument does not prove the required limiting arithmetic
estimate. This note proves an exact determinantal reformulation for the
actual two-block weight-five family and checks the directions of the
analytic and divisibility implications. No further Lean or TeX compilation
was performed. This is a paper derivation with finite arithmetic checks,
not a new complete Lean irrationality theorem.

## Analytic smallness does not bound the integer cancellation weights

The objects are different:

\[
 S_n=\max\{\mathcal A_{n,n},\mathcal A_{n,n-1}\},\qquad
 M_n=|w_0|+|w_1|.
\]

The existing analytic theorem already gives log(S_n)/n -> lambda_5<0.
In particular S_n is eventually bounded by one. That fact does not imply
log(M_n)/n -> 0. Cauchy estimates bound absolute values of coefficients;
they do not control the least integer relation between rational
coefficients without denominator and gcd estimates.

For an elementary counterexample to that general implication, consider
the entire polynomials

\[
 f_n(z)=2^{-2n}z+2^{-3n},\qquad
 g_n(z)=-2^{-n}z+2^{-3n},\qquad n\ge1.
\]

Both have supremum at most 2^(-n)+2^(-3n) on the unit disk, and their
values at zero are both 2^(-3n). Their linear coefficients are rational.
The relatively prime positive integer weights cancelling those
coefficients are (2^n,1), since

\[
 w_0\,2^{-2n}-w_1\,2^{-n}=0
       \quad\Longleftrightarrow\quad w_0=2^n w_1.
\]

Thus their weight mass is 2^n+1 and its logarithmic rate is log(2)>0,
despite uniform exponential smallness of the whole functions on a fixed
disk. This is not our zeta family; it disproves the proposed general
inference from contour bounds to subexponential integer weight mass.
Shrinking a contour also introduces its inverse radius in the Cauchy
coefficient bound, which must be included in the budget.

## An exact matrix for our constructed family

Let D=d_n^5 and clear the actual rational period-coordinate triples:

\[
 D\mathcal A_{n,n}=x_0\zeta(3)+y_0\zeta(5)+z_0,\qquad
 D\mathcal A_{n,n-1}=x_1\zeta(3)+y_1\zeta(5)+z_1.
\]

All six coordinates are integers by the denominator theorem.
The global adjacent-sign theorem gives x_0*x_1<0. Set

\[
 g=\gcd(|x_0|,|x_1|),\quad
 \Delta_5=x_1y_0-x_0y_1,\quad
 \Delta_0=x_1z_0-x_0z_1,\quad
 H=\gcd(|\Delta_5|,|\Delta_0|).
\]

The primitive integer vector cancelling the x-column is, up to its
common sign, (x_1/g,-x_0/g). Consequently

\[
 M=\frac{|x_0|+|x_1|}{g},\qquad
 (A,B)=\pm\left(\frac{\Delta_5}{g},\frac{\Delta_0}{g}\right).
\]

Since g divides both determinants, taking integer gcds gives H=g*h.
The pair of determinants is not zero, because that would make the
same-sign combination of the two positive kernel sums zero. Therefore

\[
 \boxed{\frac hM=\frac H{|x_0|+|x_1|}},\qquad
 \boxed{K=\frac{D(|x_0|+|x_1|)}H}.
\]

This proves the identity for every even n>=2. The exact audit separately
verifies it, with full integer matrices and determinants recorded, at
n=2,4,8,12,20,40,80,160. Those checks validate the implementation; the
algebra above supplies the general identity.

The determinant formula removes the intermediate gcd g from the
arithmetic target. It does not prove that H is exponentially large
relative to |x_0|+|x_1|. The sufficient estimate becomes exactly

\[
 \liminf_{n\to\infty,\ n\text{ even}}
 \frac{\log H_n-\log(|x_0|+|x_1|)}n>5+\lambda_5.
\]

## What a local common-divisor proof must establish

For every prime p, with v_p(0)=infinity,

\[
 v_p(H)=\min\{v_p(\Delta_5),v_p(\Delta_0)\}.
\]

Thus a usable construction gives explicit nonnegative integers e_(n,p)
such that p^e_(n,p) divides both determinants. This proves

\[
 \log H_n\ge\sum_p e_{n,p}\log p.
\]

One must then show that this sum exceeds the lower-row logarithmic size
by (5+lambda_5+epsilon)*n, eventually, for a fixed epsilon>0.
Showing either determinant is nonzero modulo p instead proves v_p(H)=0.
Likewise, showing either A or B is nonzero modulo p proves v_p(h)=0.
Nonvanishing modulo p therefore does not establish the proposed gcd
lower bound. Denominator valuations alone do not suffice either: the
rational pair (1/p^e,1) clears to (1,p^e), whose gcd is one.

## The direction of a resultant estimate

For coprime integer polynomials f,g, a resultant identity has the form
u*f+v*g=Res(f,g) with integer polynomials u,v. Evaluating at an integer k
proves

\[
 \gcd(|f(k)|,|g(k)|)\mid|\operatorname{Res}(f,g)|.
\]

For a nonzero resultant this gives an upper bound on the gcd of values.
It does not show that a large resultant divides that gcd. Explicitly,
take f(x)=x, g(x)=x+2^n and k=1. The resultant is 2^n, while the gcd of
the values is gcd(1,1+2^n)=1. A determinant representation alone cannot
reverse this implication.

The integral resultant identity is equation (1.3) of
[Liu-Li-Liu-Sha, Three quantities arising from Bezout's identity and
resultants of integer polynomials (2025)](https://arxiv.org/html/2506.10838v1).
The valuation upper-bound direction is also stated in
[Frenkel-Zabradi, Estimating the greatest common divisor of the value of
two polynomials](https://arxiv.org/abs/1712.01054).
These statements do not identify our coefficient determinants with
specializations of any such polynomial pair; that identification would
be a further construction, with its hypotheses checked.

Finally, h is the content removed from the integer coefficient pair,
not the height of the resulting primitive pair. That primitive pair has
gcd one. If M were proved subexponential, the sufficient rate for h would
be 5+lambda_5, between 0.029206 and 0.029207. The proposed rate 5.02920614
would be a stronger sufficient rate under that additional hypothesis,
but no such lower bound is established by the proposed resultant or
nonvanishing assertions.

The matrix and determinant identities above are proved. Their winning
growth estimate remains unproved, so the irrationality conclusion does
not yet follow.
