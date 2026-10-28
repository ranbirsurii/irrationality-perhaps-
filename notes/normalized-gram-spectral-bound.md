# Applying spectral estimates to the actual cancellation lattice

Fix an odd weight s=2r+1 and set N=r+1. The input hypotheses are the
full row rank of C_(s,n), full rank of the augmented matrix (C;Y;Z),
the established denominator bound, and the raw analytic decay estimate.
These hypotheses are not replaced here by an unconditional theorem for
all higher weights.

## The correct Gram matrix and its exact eigenvalue bounds

Let a,b be a Gauss-reduced integral basis of the saturated cancellation
lattice. Write A=norm(a)^2, B=a dot b, C=norm(b)^2. Then

\[
 G=\begin{pmatrix}A&B\\B&C\end{pmatrix},\qquad
 0<A\le C,\qquad 2|B|\le A.
\]

The ordered eigenvalues are

\[
 \mu_\pm=\frac{A+C\pm\sqrt{(C-A)^2+4B^2}}2.
\]

Their sum and product are A+C and AC-B^2. These identify the two roots of
the characteristic polynomial of this two-by-two Gram matrix. Reduction
gives 4B^2<=A^2 and

\[
 (C-A)^2\le (C-A)^2+4B^2\le C^2.
\]

For the upper inequality, expand the difference C^2 minus the middle
expression, and use A<=C and 4B^2<=A^2. Taking square roots gives
C-A<=sqrt(discriminant)<=C. Substitution proves

\[
 A/2\le\mu_-\le A,\qquad C\le\mu_+\le3C/2.
\]

This is the explicit two-dimensional instance of the Courant-Fischer
comparison. The general variational theorem is stated and proved in
[David Bindel's matrix-computations lecture](https://www.cs.cornell.edu/courses/cs6210/2025fa/lec/2025-11-03.html).

`OddZeta/GramSpectralBounds.lean` proves the root formulas' sum, product,
characteristic equations, these inequalities, the trace comparison, and
the consequence for a cost bound. It also proves

\[
 \kappa^2=\frac CA
 \le\frac{\mu_+}{\mu_-}\le3\frac CA=3\kappa^2,
 \qquad
 \mu_+\le\frac{AC-B^2}{m}\quad(0<m\le\mu_-).
\]

The last inequality gives a direct route from a quantitative lower bound
for the smallest eigenvalue to an upper bound for the largest, using the
known Gram determinant. Its lower-bound hypothesis is explicit.
For an actual nonzero integer basis vector, A>=1. In that case the module
proves the uniform, unconditional estimates

\[
 \boxed{\mu_-\ge1/2,\qquad
        \mu_+\le2(AC-B^2)=2H_n^2.}
\]

Thus this method does produce an absolute spectral gap. It bounds the
normalized largest eigenvalue by 2(H_n/Gamma_n)^2; it does not bound that
arithmetic ratio or give an exponential lower bound at the scale of H_n
for the smallest eigenvalue.
The module uses direct real algebra and square
root monotonicity for this special case rather than formalizing the entire
general Courant-Fischer theorem.

## Removing the requirement of nonnegative weights

Put Gamma=gcd(Y(a),Y(b),Z(a),Z(b))>0. The two forms

\[
 L_a=\frac{Y(a)}\Gamma\zeta(s)+\frac{Z(a)}\Gamma,
 \qquad
 L_b=\frac{Y(b)}\Gamma\zeta(s)+\frac{Z(b)}\Gamma
\]

have integer coefficients. The full augmented rank gives
Y(a)Z(b)-Y(b)Z(a)!=0 by the proved Smith determinant identity. Hence
these forms cannot both vanish. This is the elementary determinant
argument proved in the signed cancellation companion.

The cleared period expansion and the signed triangle inequality give,
for either v=a or v=b,

\[
 |L_v|\le\frac{d_n^s}{\Gamma}\|v\|_1S_n
 \le\sqrt N\,d_n^s S_n\frac{\lambda_2}{\Gamma}
 \le\sqrt N\,d_n^s S_n
       \sqrt{\frac{\mu_+(G_n)}{\Gamma_n^2}}.
 \tag{1}
\]

Here norm(v)_1<=sqrt(N)*norm(v)_2, norm(v)_2<=lambda_2=sqrt(C),
and C<=mu_+. Select a nonzero one of the two forms at each eligible index.
This replaces positivity by the explicit augmented-rank hypothesis. It
does not assume irrationality to obtain nonvanishing.

## The precise spectral estimate that would finish this route

If log(d_n)/n tends to one and log(S_n)/n has upper rate lambda_s, then
(1) gives the upper exponent

\[
 s+\lambda_s+
 \frac12\limsup\frac1n\log\frac{\mu_+(G_n)}{\Gamma_n^2}.
\]

Consequently a sufficient condition is

\[
 \boxed{\limsup\frac1n\log\frac{\mu_+(G_n)}{\Gamma_n^2}
                      <-2(s+\lambda_s).}                 \tag{2}
\]

At every fixed s>=7, the proved coarse analytic margin a_s>s+1/3 shows
that the uniform sufficient estimate

\[
 \limsup\frac1n\log\frac{\mu_+(G_n)}{\Gamma_n^2}\le1/2
                                                               \tag{3}
\]

would leave a strictly negative exponent, less than -1/12. This is a
sufficient condition, not an estimate established for the constructed
family. With the sharp saddle constant the allowed rate is slightly
larger. No numerical value from weight five is transferred to the lattice
at a different weight.

The comparison C<=mu_+<=3C/2 also proves that (2) is equivalent, at the
level of exponential rates, to a bound for lambda_2/Gamma. The constant
factor from min-max does not improve that rate by itself. Likewise
C<=trace(G)<=2C makes a normalized trace bound equivalent in rate.

## What the proposed motivic construction must supply

A rank calculation proves that the kernel is free of rank two and that
G is positive definite. It does not bound the eigenvalues as n varies.
A rational or real comparison of period spaces also does not determine
the common integer content Gamma.

An applicable motivic construction would need an actual integral lattice
identification, the images of generators or a controlled integral change
of basis, and a quantitative metric comparison yielding (2) or (3).
The existing `framed_comparison_content` theorem proves the exact content
identity once such an integral frame comparison and its scale are given.
Its hypothesis requires equality of the coefficient maps on every integer
vector; the geometric comparison and a uniform norm estimate are not
constructed by the rank proof.

For example, an explicit positive-semidefinite comparison

\[
 G_n/\Gamma_n^2\preceq C_0 e^{n/2}I_2
\]

would imply (3) directly by Courant-Fischer. No such bound follows from
positive definiteness or rank alone. The present spectral calculation
identifies exactly the quantitative comparison needed; it does not prove
an unconditional irrationality theorem.
