# Smith factors, an adjacent-family bridge, and exterior-square transport

This investigation implements the Smith-form and recurrence proposals for
the actual weight-five family. It obtains a universal adjacent-family
certificate with polynomial arithmetic cost and an exact Casoratian and
exterior-square system. It does not prove the winning gcd growth estimate
or irrationality. These are paper arguments with independently checked
polynomial certificates and finite exact lattice checks. No new Lean or
TeX compilation was performed.

## The Smith divisor and the selected minors

Use the integer coefficient matrix from the preceding note:

\[
 C_n=\begin{pmatrix}x_0&y_0&z_0\\x_1&y_1&z_1\end{pmatrix},
 \quad H_n=\gcd(x_1y_0-x_0y_1,x_1z_0-x_0z_1)>0.
\]

All gcds are nonnegative. Put m_(ij) for the ordinary 2-by-2 minors.
There are three, not two. The full determinantal divisor is

\[
 \delta_n=\gcd(m_{01},m_{02},m_{12})=\sigma_{1,n}\sigma_{2,n},
\]

the product of the two nonzero Smith factors. In general H_n is larger.
Let g_n=gcd(x_0,x_1). Then

\[
 \boxed{H_n=\delta_n E_n,\qquad E_n\mid g_n.}
 \tag{1}
\]

To prove the divisibility, the determinant identities give

\[
 x_i m_{12}=y_i m_{02}-z_i m_{01}\quad(i=0,1).
\]

Thus H_n divides g_n*m_(12) by Bezout's identity. Writing
delta_n=gcd(H_n,m_(12)), Euclid's lemma gives H_n/delta_n | g_n.
This proves (1) at every even index. Since H_n=g_n*h_n, it also gives
delta_n=h_n*t_n where t_n=g_n/E_n divides g_n.

The exact arithmetic budget is therefore

\[
 \boxed{\frac{h_n}{M_n}=
 \frac{\sigma_{1,n}\sigma_{2,n}E_n}{|x_0|+|x_1|}.}
 \tag{2}
\]

`scripts/audit_smith_lattice.py` computes actual unimodular witnesses
U_n,V_n and checks U_n*C_n*V_n=diag(sigma_1,sigma_2), including determinant
units and divisibility of the diagonal entries. It separately constructs
an adapted reduction preserving the distinguished lower-period column.
The complete integer witnesses and local valuation ledgers are in
`smith-lattice-audit.json`.

| n | E_n=H_n/delta_n | log(delta_n/(abs(x_0)+abs(x_1)))/n, approximately |
|---:|---:|---:|
| 20 | 31 | -2.641717 |
| 40 | 2501 | -2.757795 |
| 80 | 1 | -2.598641 |
| 160 | 241 | -2.689634 |

The exact rational enclosures, rather than the rounded table, are in the
JSON. The desired bound concerns the full ratio (2), whose required lower
rate exceeds 0.029206. These finite negative budgets establish neither
an eventual failure nor an eventual success.

Smith form over Z is available at each index. One cannot assume a Smith
form over Z[n] for an arbitrary polynomial matrix: Z[n] is not a PID.
For example, the ideal (2,n) is not principal. Its polynomial gcd is one,
but it does not contain one, as evaluation at n=0 proves. The matrix
[2,n] therefore has no reduction to [d,0] by unimodular operations over
Z[n]. Working over Q[n] instead requires accounting for rational
denominators before drawing conclusions about integer invariant factors.

## A universal adjacent-family identity

Retain the rational kernels

\[
 R_n^{(a)}(t)=(n!)^3
 \frac{\prod_{v=1}^{n-a}(t-v)(t+n+v)}{\prod_{j=0}^n(t+j)^5},
 \qquad a=0,1,\quad n\ge2\text{ even}.
\]

Let r_n^(a) be the rational coordinate vector in the order
(zeta(3),zeta(5),constant). Thus r_n^(0) is the coordinate vector of
the normalized block of length n, whereas n^2*r_n^(1) is the vector for
the normalized block of length n-1.

The new file `adjacent-family-bridge.json` gives 21 integer polynomials
x_0(n),...,x_20(n) and four integer polynomials q_*(n),q_0(n),q_1(n),q_2(n).
These complete coefficient lists define the following certificate.
Put X=sum_(k=0..20)x_k(n)*t^k and

\[
 D_4=\prod_{i=1}^4(t+n+i)^6,\quad
 U=t^6(t+2n),\quad V=(t-n)(t+n+4)^6,
\]

\[
 H_\ell=(t-n)(t+2n)
  \prod_{i=1}^{2\ell}(t-n-i)
  \prod_{i=1}^{4\ell}(t+2n+i)
  \prod_{i=2\ell+1}^{4}(t+n+i)^6.
\]

The universal integer-polynomial identity is

\[
 \boxed{U X(n,t+1)-V X(n,t)
       =q_*D_4+\sum_{\ell=0}^2q_\ell H_\ell.}
 \tag{3}
\]

The independent verifier expands all coefficients in Z[n,t] and checks
(3), without SymPy or evaluation at sampled n. The optional symbolic
discovery solved a polynomial nullspace over Z[n]; it is not relied on
by the independent check.

For its interpretation, put B=R_n^(1)/D_4, G=V*X*B and
F_ell=product_(i=1..2ell)(n+i)^3. Cancellation of the explicit products
gives

\[
 \frac{B(t+1)}{B(t)}=
 \frac{t^6(t+2n)}{(t-n+1)(t+n+5)^6},\qquad
 BH_\ell=R_{n+2\ell}^{(0)}/F_\ell.
\]

Hence (3) implies the rational-function identity

\[
 G(t+1)-G(t)=q_*R_n^{(1)}(t)
            +\sum_{\ell=0}^2(q_\ell/F_\ell)R_{n+2\ell}^{(0)}(t).
 \tag{4}
\]

The functions G have only nonpositive integer poles, G(1)=0 because
R_n^(1)(1)=0, and G(t)=O(t^(-3n-4)) as t->infinity. Summing (4) over
positive integers therefore has zero boundary. To identify rational
coordinates without assuming independence of periods, first apply the
functionals summing the third- and fifth-order Laurent coefficients.
They vanish on G(t+1)-G(t) by finite pole-orbit cancellation. The remaining
rational coordinate is -G(1)=0, either by finite telescoping or the
harmonic-number partial-fraction formula. Thus

\[
 \boxed{r_n^{(1)}=\sum_{\ell=0}^2 c_\ell(n)r_{n+2\ell}^{(0)},
 \qquad c_\ell=-q_\ell/(q_*F_\ell).}
 \tag{5}
\]

No linear independence of 1,zeta(3),zeta(5) is used. The certificate
coefficient lists prove q_*(n)<0 and q_ell(n)>0 for n>=2, so c_ell>0.
Their initial values at n=2 are

\[
 (c_0,c_1,c_2)=\left(
 \frac{26290185784435}{5068227499224},
 \frac{13817026661819}{236517283297120},
 \frac{3858562125}{662248393231936}\right).
\]

The common positive integer denominator

\[
 b(n)=-q_*(n)\prod_{i=1}^4(n+i)^3
\]

has degree 33, and b(n)*c_ell(n) are integer polynomials. Therefore its
logarithmic cost divided by n tends to zero. The same holds after the
n^2 scaling for the actual second block. This is a proved polynomial
cost for the bridge itself; it does not prove subexponential growth of
the primitive lower-period cancellation weights.

## The full coefficient recurrence and exterior-square system

The existing offset-zero certificate also has G(1)=0 and the same
decay at infinity. The boundary argument above extends its scalar
recurrence from the third-order coefficient to all three rational
coordinates:

\[
 \sum_{\ell=0}^3P_\ell(n)r_{n+2\ell}^{(0)}=0.
\]

Here the P polynomials are exactly those already specified in
`pade-sign-recurrence-0.json`. Define F_n with successive rows
r_n^(0),r_(n+2)^(0),r_(n+4)^(0), and put

\[
 a=-P_0/P_3,\quad b=-P_1/P_3,\quad c=-P_2/P_3,\qquad
 T_n=\begin{pmatrix}0&1&0\\0&0&1\\a&b&c\end{pmatrix}.
\]

Then F_(n+2)=T_n*F_n. Taking determinants gives the exact Abel identity

\[
 W_{n+2}=(-P_0(n)/P_3(n))W_n,\qquad
 W_2=\frac{10347631144249}{324000}>0.
 \tag{6}
\]

The coefficient sign certificates show -P_0/P_3>0, so W_n is nonzero
at every even n>=2. In particular the three-coordinate recurrence state
has full rank at every such index. Its complete determinant is the
explicit product of the factors in (6).

More directly relevant to the proposed minors, let C_2 denote the second
compound matrix, indexed by pairs (01,02,12). Cauchy-Binet gives

\[
 C_2(F_{n+2})=
 \begin{pmatrix}0&0&1\\-a&0&c\\0&-a&-b\end{pmatrix}C_2(F_n).
 \tag{7}
\]

The two-block wedge in (5) is exactly c_1 times row 01 of C_2(F_n) plus
c_2 times row 02. Multiplying by d_n^10*n^2 and adjusting the ordinary
minor sign gives the actual selected minors of C_n. This explicitly
identifies the proposed Wronskian construction with the arithmetic
determinants of interest, including its normalization factors.

After clearing the recurrence denominator, (7) is an integer polynomial
matrix relation:

\[
 P_3(n)^2 C_2(F_{n+2})=C_2(P_3(n)T_n)C_2(F_n).
\]

It supplies a concrete starting point for local lattice propagation.
It does not by itself prove a favorable common-divisor rate: valuations
of P_3 and of the entries of the compound transfer must be accounted for.
Real signs and determinant magnitude alone do not supply these valuations.

## A contemporary p-adic algorithm and its boundary issue

The positive sums have an exact hypergeometric presentation:

\[
 \mathcal A_{n,m}=T_{n,m}(m+1)\,
 {}_7F_6\left(\begin{matrix}(m+1)^6,n+2m+2\\(n+m+2)^6\end{matrix};1\right),
\]

where the superscript 6 denotes six repetitions of the parameter. This
follows from the exact ratio of successive summands. It identifies an
input for the 2026 hypergeometric valuation algorithms, but their p-adic
evaluation domain must be checked before applying them at 1.

For every fixed n,m and every prime p, if p^e>n+m, direct valuations of
the kernel products give

\[
 \boxed{v_p(T_{n,m}(p^e))=v_p\binom{n+m}{m}-5e.}
 \tag{8}
\]

Indeed v_p(p^e+j)=v_p(j) and v_p(p^e-v)=v_p(v) for the fixed nonzero
integer offsets appearing in the products. Their factorial valuations
cancel to the binomial term in (8). The right side tends to minus
infinity, so the individual terms do not tend to zero p-adically.
The ordinary p-adic series at argument 1 consequently does not converge.

The associated generating series has p-adic radius exactly one: its
rational-function coefficients have at most polynomial p-adic growth,
giving radius at least one; the subsequence (8) gives the opposite bound.
The real period is at the boundary of that disk. An integral continuation
or a specified regularization and comparison would be needed to use its
p-adic realization there. This does not prevent coefficientwise finite
valuation calculations or other p-adic constructions.

## Contemporary sources and checked scope

- [Noferini-Williams, Smith forms of matrices in Companion Rings (2025)](https://arxiv.org/abs/2408.08662)
  gives Smith tools for polynomial expressions in companion matrices over
  elementary divisor domains. The full determinantal divisor, rather than
  our selected H alone, is controlled by the invariant factors.
- [Noferini, Eventual periodicity of the Smith forms of integer matrix powers (2025 preprint)](https://arxiv.org/html/2511.22814v1)
  treats powers of a fixed integer square matrix. Our exact transfer T_n
  varies rationally with n. Replacing it by its limiting constant matrix
  would not establish the required equality of integral lattices.
- [Caruso-Fuernsinn, Algorithms for Algebraic and Arithmetic Attributes of Hypergeometric Functions (2026)](https://arxiv.org/html/2601.16105v2)
  computes valuations and p-adic evaluations on disks inside the
  convergence radius; see Section 2.4. The direct evaluation at 1 in the
  displayed representation encounters (8).

The independent bridge checker verifies the universal polynomial identity,
six exact period-coordinate and exterior-square cases, and 64 finite
checks of (8). The boundary and lattice arguments in this note supply the
general mathematical statements. The Smith checker records eight complete
unimodular witnesses. Neither checker asserts a limiting gcd bound.

The next arithmetic quantity is now fully explicit: local invariant
factors of the integral recurrence lattice in (7), together with the
selected-minor factor E_n and the bridge denominator. Their combined
growth relative to the lower-period row remains to be estimated. The
irrationality theorem has not been concluded.
