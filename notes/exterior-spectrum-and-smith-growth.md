# Exterior spectrum and arithmetic invariant growth

The characteristic polynomial requested in the spectral proposal can be
computed exactly. The asserted equality between its real spectral radius
and the growth of Smith factors is false. This note proves the failure
for powers of the very same constant limiting companion matrix and gives
an elementary local-lattice computation of their actual determinantal
divisor. Neither that constant model nor its arithmetic rate is identified
with the varying coefficient lattice of the zeta construction.

These are paper proofs with exact computational checks in
`scripts/audit_exterior_spectrum.py` and `exterior-spectrum-audit.json`.
No unconditional irrationality theorem or completed Lean formalization
is claimed. No further Lean or TeX compilation was performed.

## Exact limiting characteristic polynomials

The leading coefficients of the certified recurrence give

\[
 T_n\longrightarrow A=
 \begin{pmatrix}0&1&0\\0&0&1\\729&-15146217&-30510\end{pmatrix}.
\]

This is the transfer for the original coefficient sequence; its
sign-normalized version has the corresponding signs changed. Direct
determinant expansion gives

\[
 \chi_A(z)=z^3+30510z^2+15146217z-729.
\]

In the pair basis (01,02,12), the second compound is

\[
 B=C_2(A)=
 \begin{pmatrix}0&0&1\\-729&0&-30510\\0&-729&15146217\end{pmatrix},
\]

and

\[
 \boxed{\chi_B(z)=z^3-15146217z^2-22241790z-531441.}
 \tag{1}
\]

There is a root in each of (-2,-1), (-1,0), and
(15146218,15146219), as exact endpoint sign changes show. Since the
degree is three, these are all the roots and the positive root is the
spectral radius. Rational bisection and rational logarithm enclosures
give

\[
 16.533261452721<\log\rho_B<16.533261452722.
\]

The original recurrence steps from n to n+2. Thus even an applicable
spectral norm growth theorem would give the per-original-index rate

\[
 \tfrac12\log\rho_B\in
 (8.266630726360,8.266630726361).
\]

This is a real spectral rate of the constant limiting operator. It is
not a calculation of an integer gcd or of the Smith factors of C_n.

## Exact arithmetic of powers of the limiting matrix

For any integer matrix M of rank at least two, let delta_2(M) denote the
nonnegative gcd of all its 2-by-2 minors. It is the product of its first
two nonzero Smith factors. For the matrix A above there is a complete
formula:

\[
 \boxed{\delta_2(A^k)=27^{k-1}\qquad(k\ge1).}
 \tag{2}
\]

Here is an all-k proof, independent of extrapolation from finite powers.
Define

\[
 D=\operatorname{diag}(1/27,1,1),\qquad
 K=\begin{pmatrix}0&0&1\\-1&0&-1130\\0&-27&560971\end{pmatrix}.
\]

Direct multiplication proves the rational conjugacy

\[
 B=27DKD^{-1},\qquad B^k=27^k DK^kD^{-1}.
 \tag{3}
\]

Every entry of the last matrix is an integer multiple of 27^(k-1):
the diagonal ratios from D have denominators dividing 27. Modulo 3,

\[
 K\equiv\begin{pmatrix}0&0&1\\2&0&1\\0&0&1\end{pmatrix}.
\]

Both the first and third rows are (0,0,1), and this row is fixed by
right multiplication by K modulo 3. Induction therefore gives
(K^k)_(0,2)=1 modulo 3 for every k>=1. The (0,2) entry of B^k is
27^(k-1)*(K^k)_(0,2), so its 3-adic order is exactly 3k-3. Thus

\[
 v_3(\gcd\text{ entries of }B^k)=3k-3.
\]

There are no other primes in this gcd: det(B^k)=3^(12k), and a prime
dividing every entry of a square integer matrix must divide its
determinant. Hence the gcd of the entries is exactly 27^(k-1).
Finally, Cauchy-Binet gives C_2(A^k)=C_2(A)^k=B^k, proving (2).

It follows that

\[
 \lim_{k\to\infty}\frac{\log\delta_2(A^k)}{2k}
  =\tfrac12\log27\in(1.647918433002,1.647918433003).
 \tag{4}
\]

Equations (1)-(4) give different real spectral and arithmetic invariant
growth rates for the same limiting transfer matrix. The missing
information is the integral lattice, not another real characteristic
polynomial calculation. The checker verifies the rational conjugacy,
the modular identities used by the induction, and (2) at the first
twenty powers. The conjugacy and induction above prove all powers.

## A large spectral radius can coexist with no invariant growth

An even simpler universal counterexample addresses the proposed threshold
implication. Let

\[
 U=\begin{pmatrix}1000&1&0\\999&1&0\\0&0&1\end{pmatrix}.
\]

It has determinant one, so U^k is unimodular for every k>=0 and all its
Smith factors are one. Nevertheless its eigenvalues are 1, lambda, and
lambda^(-1), where lambda is the larger root of z^2-1001z+1.
The polynomial is negative at 1000 and positive at 1001, so

\[
 \rho(C_2(U))=\lambda\in(1000,1001),\qquad
 \sigma_1(U^k)\sigma_2(U^k)=1.
\]

Consequently even an arbitrarily favorable real spectral radius does
not force a positive common-divisor growth rate. This example is not
asserted to be the zeta family; it disproves the proposed general
spectral-to-Smith implication.

## The arithmetic estimate that still concerns the actual family

For our actual two-block integer coefficient matrix C_n, the previous
lattice calculation proves

\[
 \frac{h_n}{M_n}
 =\frac{\sigma_{1,n}\sigma_{2,n}E_n}{|x_{0,n}|+|x_{1,n}|}.
\]

Thus the sufficient bound is

\[
 \boxed{\liminf\frac{
 \log(\sigma_{1,n}\sigma_{2,n})+\log E_n
 -\log(|x_{0,n}|+|x_{1,n}|)}n>5+\lambda_5.}
 \tag{5}
\]

The lower-period row cannot be omitted. Nor can the clearing factor be
silently absorbed into the unnormalized spectral operator: multiplying
a coefficient matrix by d_n^5 multiplies its 2-by-2 minors by d_n^10.
Those changes must be tracked in any integral comparison.

There is also a numerical correction: with the established convention
lambda_5 in (-4.970794,-4.970793),

\[
 5+\lambda_5\in(0.029206,0.029207),
\]

not 5.02920614. This correction does not establish (5).

The exact variable recurrence T_n and the bridge from the adjacent
family were proved in the preceding note. Replacing their integral
lattice by powers of A is a further unproved comparison. Formula (2)
is a result about that constant model only; it neither proves nor
disproves (5) for the actual family.

## Relation to the literature

[Elsheikh-Giesbrecht, Relating p-adic eigenvalues and the local Smith
normal form](https://arxiv.org/html/1401.1773v4) establishes conditions
for a relation between p-adic eigenvalue valuations and local Smith
factors, and gives counterexamples without those conditions. This is a
local arithmetic statement; it is not the asserted equality with the
ordinary real spectral radius.

[Noferini, Eventual periodicity of the Smith forms of integer matrix
powers](https://arxiv.org/html/2511.22814v1) proves eventual structure for
the Smith forms of powers of a fixed integer matrix. Its statement does
not replace their arithmetic growth rate by the real spectral radius.
Our exact formula (2) is a direct local calculation in one such fixed
matrix example.

The requested characteristic polynomial has been computed and the
constant-model arithmetic has been solved exactly by integral conjugacy.
The proposed shortcut to (5) is false. The arithmetic estimate needed
for the irrationality proof remains unproved; no final irrationality
Lean theorem or arXiv-ready proof manuscript follows from this step.
