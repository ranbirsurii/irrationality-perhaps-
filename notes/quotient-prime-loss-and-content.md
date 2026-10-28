# Bounded quotient-prime losses and the remaining content estimate

This note proves a uniform statement about exceptional primes, rather
than extrapolating from finite indices. It also gives a strictly positive
matrix example that separates Perron growth from integer content. Neither
statement proves the outstanding primitive-cost estimate. In particular,
the local divisibility estimate and the cost of positive integer weights
are not assumed to follow from the exceptional-prime statement.

## A bounded exceptional-prime loss is sublinear

Let I be any subset of the positive integers, and fix a nonzero integer
R_q for every q in I. Put

\[
 E_n=\{p\le n:p\text{ prime},\ q=\lfloor n/p\rfloor\in I,
                         \ p\mid R_q\}.
\]

For arbitrary numbers 0<=ell_(n,p)<=b, with b a fixed constant, one has

\[
 \boxed{\sum_{p\in E_n}\ell_{n,p}\log p=o(n).}                 \tag{1}
\]

No bound on the growth of R_q as q tends to infinity is required.

Proof. Fix an integer L>=1 and define the positive integer

\[
 P_L=\prod_{\substack{q\in I\\q\le L}}|R_q|,
\]

with the empty product equal to one. For n>=(L+1)P_L, a prime in E_n
cannot have q<=L: otherwise p<=P_L and
n<(q+1)p<=(L+1)P_L. Therefore q>=L+1 and p<=n/(L+1). Writing
theta(x)=sum_(p<=x)log(p), this gives the explicit bound

\[
 \sum_{p\in E_n}\ell_{n,p}\log p
       \le b\,\theta\!\left(\frac n{L+1}\right)
       \le\frac{4b\log2}{L+1}\,n.                              \tag{2}
\]

The elementary Chebyshev bound in (2) follows by grouping primes in
dyadic intervals: the primes m<p<=2m divide binom(2m,m)<=4^m, so
theta(2m)-theta(m)<=2m*log(2). Summing for m=1,2,... along powers
of two and rounding x upward to the next power of two gives
theta(x)<=4x*log(2). First let n tend to infinity in (2), then let L
tend to infinity. This proves (1), including its quantifiers. The
cutoff (L+1)P_L is finite and explicit even when it is very large.

For the actual weight-five family take I to be the positive even
integers and

\[
 R_q=\left|\operatorname{numerator}(a_3(q,q))\right|.
\]

The global coefficient-sign theorem proves R_q>0 for every such q.
Consequently the even-quotient exceptional set that contains the
previously found pair n=480, p=47 has total log-prime weight o(n).
This conclusion applies to bounded losses, not to an uncapped quantity
such as the full valuation of a_3(q,q). An identically zero odd-quotient
coefficient cannot be put into this lemma as a nonzero R_q.

## The exact local statement that would give the content rate

Retain Gamma_n, the positive content of the image of the saturated
integer cancellation lattice. For a prime p<=n define

\[
 c_{n,p}=\left\lfloor\frac{3n}{2p}\right\rfloor
                  -3\left\lfloor\frac n{2p}\right\rfloor
       \in\{0,1,2\},\qquad
 \delta_{n,p}=\max\{0,2+c_{n,p}-v_p(\Gamma_n)\}.
\]

Thus 0<=delta_(n,p)<=4. Suppose one could prove the following
specific assertion for every even n sufficiently large:

For every p<=n with p^2>3n+6 and p not dividing
B_n=n(n-1)(n-2)*product_(j=0..12)(3n-j), either p belongs to the
even-quotient set E_n above, or

\[
                 v_p(\Gamma_n)\ge2+c_{n,p}.                    \tag{3}
\]

Then (1), with b=4, proves that the total loss from E_n is o(n).
The small primes cost at most 4*theta(sqrt(3n+6))=o(n), and the
boundary primes cost at most 4*log(B_n)=O(log(n)). It follows that

\[
 \log\Gamma_n\ge
       \sum_{p\le n}(2+c_{n,p})\log p-o(n).                    \tag{4}
\]

Here is a derivation of the rate in (4). Write n=2k. Legendre's
formula for (3k)!/(k!)^3 gives

\[
 \log\frac{(3k)!}{(k!)^3}
 =\sum_p\sum_{a\ge1}
       \left(\left\lfloor\frac{3k}{p^a}\right\rfloor
                     -3\left\lfloor\frac{k}{p^a}\right\rfloor\right)
       \log p.
\]

Every coefficient is between zero and two. Terms with a>=2 total
O(sqrt(n)*log(n)) and hence are o(n). For p>n, the first-power
coefficient is one exactly on n<p<=3n/2. Stirling's formula and the
prime number theorem consequently give

\[
 \frac1n\sum_{p\le n}c_{n,p}\log p
          \longrightarrow\frac32\log3-\frac12.
\]

Therefore (3) would imply the precise estimate

\[
 \liminf_{n\to\infty,\ n\text{ even}}\frac{\log\Gamma_n}{n}
                 \ge\frac32+\frac32\log3.                    \tag{5}
\]

Statement (1) is proved. Statement (3) is not proved. The existing
first-order congruence makes suitably scaled coordinate rows collinear
modulo p; it does not by itself give the higher powers in (3) after
division by the lower-row gcd. Nor does it prove that all failures of
(3) are supported on E_n. No such support assertion is being added
as an implicit hypothesis of the final irrationality theorem.

For completeness, one can derive the precise weaker local bound that
the existing congruence does prove. At an eligible prime p<=n, set

\[
 X_i=p^2a_3(n,n-i),\qquad Y_i=a_5(n,n-i),\qquad
 Z_i=p^5b(n,n-i),\qquad i=0,1,2.
\]

These coordinates are p-integral and their three rows are collinear
modulo p. Therefore both X_i*Y_j-X_j*Y_i and X_i*Z_j-X_j*Z_i are
divisible by p. Since p^2>n, write d_n^5=p^5*u with u a p-adic unit.
The cleared integer coordinates are

\[
                  (x_i,y_i,z_i)=(p^3uX_i,p^5uY_i,uZ_i).
\]

Every selected x-y minor thus has valuation at least nine and every
selected x-z minor has valuation at least four. The exact content
identity g_n*Gamma_n=gcd(all selected minors) proves

\[
 \boxed{v_p(\Gamma_n)\ge\max\{0,4-v_p(g_n)\}.}               \tag{7}
\]

This is unconditional under the stated eligibility conditions. For
example, when v_p(g_n)=3 it gives one power of p, whereas (3) asks for
at least two. In scaled coordinates, (3) requires the x-z determinants
to have valuation at least v_p(g_n)-1+c_(n,p), together with the
corresponding x-y condition. Collinearity modulo p supplies only one
power, so the extra powers have not been obtained by the first-order
argument. This locates the missing congruence without discarding the
effect of primitive normalization.

## The positive-weight cost must still be controlled

All limits in this section are along the positive even indices.

Let b_0,b_1 be a Gauss-reduced basis of the saturated kernel of the
integer lower-period row x, set g=gcd(x), and put

\[
 \kappa_n=\frac{\|b_1\|_2}{\|b_0\|_2}\ge1,\qquad
 Q_n=\|b_0\|_1+\|b_1\|_1.
\]

Its covolume is norm(x/g). Reduction gives an angle with sine at
least sqrt(3)/2. The inequalities between the one- and two-norms give

\[
 Q_n\le2\sqrt3\|b_1\|_2
      \le2\sqrt{2\sqrt3}\sqrt{\kappa_n\|x/g\|_2}
      \le4\sqrt{\kappa_n\|x/g\|_2}.                            \tag{6}
\]

For the selected nonzero nonnegative integer vector w=s*b_0+t*b_1,
let J_n=max(abs(s),abs(t)). The exact algebra already proved yields

\[
 K_n\le d_n^5J_nQ_n/\Gamma_n.
\]

If (5) were established, the proved primitive-normal upper bound
would combine with (6) to give

\[
 \limsup\frac{\log K_n}{n}
 \le c_*+\limsup\frac{\log J_n+\tfrac12\log\kappa_n}{n},
\]

where

\[
 c_*=5+\frac12(5+3\log6-c_g)
                     -\left(\frac32+\frac32\log3\right),\qquad
 c_g=3+\frac{\pi}{4\sqrt3}+\frac34\log3.
\]

In particular subexponential J_n and kappa_n would be sufficient,
but neither has been established. The sharper formulation is a single
combined cost condition

\[
 \limsup\frac{\log J_n+\tfrac12\log\kappa_n}{n}
                        <\log140-c_*.
\]

Together with (5), this would make the proved analytic bound
C_0*(n+1)^12*K_n/140^n tend to zero. This is an explicit conditional
implication, not a proof of its two arithmetic premises. Likewise
Gamma_n>=exp(n/10)*J_n*Q_n is sufficient; it is not equivalent to
an upper bound on K_n, since h_n can be strictly larger than Gamma_n.

## Strict positivity does not repair spectral-to-content inference

For any integer H>=2 define the unimodular matrix

\[
 L_H=\begin{pmatrix}1&0&0\\H&1&0\\H&H&1\end{pmatrix},\qquad
 U_H=L_HL_H^T=
 \begin{pmatrix}
 1&H&H\\H&H^2+1&H^2+H\\H&H^2+H&2H^2+1
 \end{pmatrix}.
\]

Both U_H and its second compound are strictly positive entrywise.
Indeed direct determinant expansion gives

\[
 C_2(U_H)=
 \begin{pmatrix}
 1&H&H^2-H\\
 H&H^2+1&H^3-H^2+H\\
 H^2-H&H^3-H^2+H&H^4-2H^3+2H^2+1
 \end{pmatrix}.
\]

Since det(U_H)=1, all Smith factors of U_H^k equal one for every
k>=1. Equivalently the gcd of the entries of C_2(U_H)^k is one.
However symmetry and the Rayleigh quotient give

\[
 \rho(C_2(U_H))\ge H^4-2H^3+2H^2+1\longrightarrow\infty.
\]

Thus even a constant, strictly positive, irreducible exterior system
with arbitrarily large Perron root need not have any determinantal
gcd growth. This covers the extra positivity hypotheses in the proposed
spectral argument; the example is not being identified with the zeta
coefficient matrix.

The same family separates Mahler measure from content. The eigenvalues
of U_H are positive and its largest is at least 2H^2+1, so the Mahler
measure of its monic characteristic polynomial is at least 2H^2+1.
Nevertheless its powers still have unit Smith factors. For H>=3 that
characteristic polynomial is nonreciprocal: its coefficients of z^2
and z are respectively -(3H^2+3) and H^4-2H^3+3H^2+3, which do
not have equal absolute values. A large Mahler measure, even in this
nonreciprocal case, does not force the required common divisibility.
The periods themselves have no supplied algebraicity theorem from
which one could construct their proposed minimal polynomials.

The relevant p-adic eigenvalue/Smith-form literature also imposes
conditions; it does not assert correspondence for arbitrary matrices:
[Elsheikh and Giesbrecht, Relating p-adic eigenvalues and the local
Smith normal form](https://arxiv.org/html/1401.1773v4).
Similarly the denominator theorem of
[Krattenthaler and Rivoal](https://arxiv.org/abs/math/0311114)
concerns specified hypergeometric forms and supplies no automatic
identification with this image content after cancellation.

The most direct unresolved method here is an explicit higher-order
local congruence for the six selected minors, including the exact loss
from dividing by g_n, followed by a positive-lattice cost estimate.
The exceptional-prime lemma proves one part of that program. It does
not finish either missing estimate, and no completed irrationality
proof or Lean theorem is claimed. No finite-index tests or compilation
were performed in deriving these results.
