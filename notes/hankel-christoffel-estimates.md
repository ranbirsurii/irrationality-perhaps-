# Exact approximation estimates at every odd weight

These estimates concern the actual tail-moment coefficients already defined
in `OddHankelArithmetic.lean`. They require no geometric comparison and no
irrationality hypothesis. The method uses the positive-functional viewpoint
of [Ferguson, Rational Approximations via Hankel Determinants](https://arxiv.org/html/2003.10616),
with a direct Jacobi calculation for this particular measure.

Let `s=2r+1`, `r>=1`, `a>=0`, and `N>=1`. Retain

\[
\Delta_{N,a}^{(s)}=A_{N,a}^{(s)}\zeta(s)+B_{N,a}^{(s)},\qquad A_{N,a}^{(s)}>0.
\]

Define `(z)_k=z(z+1)...(z+k-1)`, with `(z)_0=1`, and put

\[
E_{N,a}=\frac{\Delta_{N,a}^{(s)}}{A_{N,a}^{(s)}}
=\zeta(s)+\frac{B_{N,a}^{(s)}}{A_{N,a}^{(s)}}.
\]

For every `N>r` the following finite bounds hold:

\[
\boxed{\quad
\frac{(2r-1)!}{(N)_{2r}(N+a)_{2r}}
\ \le E_{N,a}\le\
\frac{(2r-1)!}{(N-r)_{2r}(N-r+a)_{2r}}.
\quad}
\tag{1}
\]

The lower bound holds for every `N>=1`. In particular, for **any** sequence
of nonnegative integer shifts `a_N`, including growing shifts,

\[
N^{2r}(N+a_N)^{2r}E_{N,a_N}\longrightarrow(2r-1)!.
\tag{2}
\]

## 1. The determinant ratio is a minimum

Write

\[
\rho(x)=\frac{x^a(-\log x)^{2r}}{(2r)!(1-x)}.
\]

The moment matrix is the positive Gram matrix of polynomials of degree
less than `N` in this weight. Change its basis to

\[
1,\quad 1-x,\quad x(1-x),\quad\ldots,\quad x^{N-2}(1-x).
\]

The transformation has determinant of absolute value one. The determinant
of the lower-right block is exactly `A`, since the differences of moments
give the coefficient matrix in the existing construction. Completing the
square in the resulting positive block matrix gives its Schur complement:

\[
\frac{\Delta}{A}
=\min_{\deg P<N,\ P(1)=1}\int_0^1P(x)^2\rho(x)\,dx.
\tag{3}
\]

For `N=1` this states that the only admissible polynomial is `P=1`.
All integrals are finite, since the original measure is finite and
polynomials are bounded on the interval.

## 2. An explicit Jacobi minimum

For integers `m,b>=0`, set `w(x)=x^b(1-x)^m`. The minimum in (3) for
this weight is

\[
\lambda_N^{(m,b)}(1)
=\frac{m!(m+1)!}{(N)_{m+1}(N+b)_{m+1}}.
\tag{4}
\]

Here is a derivation with all normalizations specified. Define

\[
J_j(x)=\frac{(-1)^j}{j!x^b(1-x)^m}
\frac{d^j}{dx^j}\bigl[x^{b+j}(1-x)^{m+j}\bigr].
\]

The quotient is a polynomial of degree `j`. Its leading coefficient is
`binom(2j+m+b,j)`, and `J_j(1)=binom(j+m,j)`. Integrating by parts `j`
times proves orthogonality against every polynomial of smaller degree;
the boundary terms vanish because the differentiated expression starts
with zeros of order at least `j` at both endpoints. The same calculation
and the elementary beta integral give

\[
h_j=\int_0^1J_j(x)^2w(x)\,dx
=\frac{(j+m)!(j+b)!}{(2j+m+b+1)j!(j+m+b)!}.
\]

Writing `P=sum c_j J_j`, Cauchy-Schwarz gives

\[
1=P(1)^2\le\Bigl(\sum c_j^2h_j\Bigr)
\Bigl(\sum_{j<N}J_j(1)^2/h_j\Bigr).
\]

Equality is attained by choosing `c_j` proportional to `J_j(1)/h_j`.
The second factor telescopes:

\[
\sum_{j<N}\frac{(2j+m+b+1)(j+m)!(j+m+b)!}{m!^2j!(j+b)!}
=\frac{(N)_{m+1}(N+b)_{m+1}}{m!(m+1)!}.
\]

One checks the identity by subtracting the expression at `N=j` from its
value at `N=j+1`, with the term at `N=0` equal to zero. This proves (4).
The norm convention also agrees with
[NIST DLMF Table 18.3.1](https://dlmf.nist.gov/18.3#T1) after shifting the interval.

## 3. Weight comparison proves the bounds

For `0<x<1`, the elementary logarithm inequalities are

\[
1-x\le-\log x\le(1-x)/x.
\]

Taking the power `2r` and setting

\[
q(x)=\frac{x^a(1-x)^{2r-1}}{(2r)!}
\]

gives `q<=rho` and `x^(2r)rho<=q`. Thus (3) is at least the Jacobi minimum
for `q`. For the upper bound, restrict its admissible polynomials to
`P=x^r Q`, with `deg Q<N-r` and `Q(1)=1`. Then

\[
\int P^2\rho=\int Q^2x^{2r}\rho\le\int Q^2q.
\]

Apply (4) with `m=2r-1`, `b=a`, and divide by `(2r)!`. This proves (1).

For uniformity in `a`, use the elementary product bounds

\[
N^k\le(N)_k\le(N+k-1)^k.
\]

For `k=2r`, the scaled quantity in (2) lies between

\[
(2r-1)!\left(\frac{N}{N+2r-1}\right)^{4r}
\quad\text{and}\quad
(2r-1)!\left(\frac{N}{N-r}\right)^{4r}.
\]

These bounds are independent of `a>=0` and both tend to `(2r-1)!`.
This proves (2), even for shifts growing arbitrarily quickly.

## 4. A proved arithmetic saving by rowwise clearing

Write `M=a+2N-2` and `d_j=lcm(1,...,j)`, with `d_0=1`. For row `i`, all
indices `a+i+j` are at most `M_i=a+i+N-1`. Therefore the smaller integer
`D_i=d_(M_i)^s` clears that entire row. Set

\[
D_{\rm row}=\prod_{i=0}^{N-1}d_{a+i+N-1}^{s},\qquad
G_{\rm row}=\prod_{i=0}^{N-1}\left(\frac{d_M}{d_{a+i+N-1}}\right)^s.
\]

Every quotient is an integer, and `G_row D_row=d_M^(sN)=Q^N`. Define the
integer matrix `W(y)` by

\[
W(y)_{ij}=D_i y-\sum_{k=1}^{a+i+j}(d_{M_i}/k)^s,
\quad U'=\det W(1)-\det W(0),\quad V'=\det W(0).
\]

Factoring `D_i` from each row over the rationals and using determinant
affinity proves

\[
D_{\rm row}\Delta=U'\zeta(s)+V',\qquad
U=G_{\rm row}U',\quad V=G_{\rm row}V'.
\]

In particular, this constructs an unconditional common divisor:

\[
G_{\rm row}\mid g,\qquad
g=G_{\rm row}\gcd(|U'|,|V'|).
\tag{5}
\]

No cancellation estimate is assumed. Its exact remaining prime cost is

\[
v_p(D_{\rm row})=s\sum_{i=0}^{N-1}\lfloor\log_p(a+i+N-1)\rfloor.
\]

At an index equal to zero the summand means zero, corresponding to `d_0=1`.
Using only the elementary lcm bound already proved in the repository gives

\[
\log D_{\rm row}\ge s\sum_{i=0}^{N-1}
\bigl((a+i+N-1)\log2-\log(a+i+N)\bigr).
\]

`RowwiseHankelArithmetic.lean` proves the change-of-scale identity for the
finite harmonic sums, the determinant and coefficient factorizations,
the exact gcd factorization, and these finite prime and logarithmic costs.
This gives a genuinely cheaper integral presentation. The primitive pair
is the same after its complete gcd is removed.

## 5. What is left after these estimates

For the actual integer row `U=Q^N A`, `V=Q^N B`, let
`g=gcd(abs(U),abs(V))` and `u=U/g>0`. The primitive real form is exactly

\[
\ell=\frac{Q^N}{g}\Delta=uE_{N,a}.
\]

Hence (2) gives the equivalence

\[
\boxed{\quad
\ell_{N,a_N}\to0
\quad\Longleftrightarrow\quad
\frac{u_{N,a_N}}{N^{2r}(N+a_N)^{2r}}\to0.
\quad}
\tag{6}
\]

Equivalently, the gcd must grow sufficiently that
`g N^(2r)(N+a_N)^(2r)/U` tends to infinity. This is a specific arithmetic
estimate on the constructed integer row, rather than a remaining analytic
decay estimate. It has not been proved here. Geometric comparison would have
to transfer a theorem controlling this particular primitive height.

The January 2026 revision of
[Brown-Zudilin, On cellular rational approximations to zeta(5), Theorem 1](https://arxiv.org/html/2210.03391v3)
uses a different cellular-integral family and symmetry-controlled
denominators. Its exponent `0.86` cannot be inserted into (6), since the
coefficient rows and approximation parameters are different. The theorem
also does not assert the stronger integer-form decay required here.

`HankelEndpointEstimates.lean` verifies the logarithm inequalities, their
power versions, the actual pointwise weight sandwich, ascending-factorial
bounds, and the rational lower-bound expression. The Schur complement,
Jacobi orthogonality, integration, and limit arguments above are ordinary
mathematical proofs and are not claimed as Lean-verified.

The exact audit `scripts/endpoint_error_audit.py` checks (1) and the identity
`ell=uE` using rational zeta intervals, at weights 3, 5, 7, and 9, sizes 5,
10, and 20, and shifts zero and the size. Finite checks do not prove (6)'s
arithmetic condition or the all-odd irrationality theorem.
