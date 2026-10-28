# Arithmetic refinement of the proposed strategies

This note applies the denominator and telescoping proposals to the actual
well-poised kernels. It does not prove irrationality of every odd zeta value.
The general denominator theorem below is a paper proof. The accompanying
Lean module proves the binomial formula for the displayed leading-coefficient
magnitude, the block recurrence, positivity of convergent combinations with
nonnegative weights, and invariance of primitive cost under excess clearing.
It does not formalize the complete Taylor-coefficient denominator theorem.

## An all-index denominator theorem for these kernels

Let s=2r+1>=3, let n be even, and let 0<=m<=n. Put

\[
 d_n=\operatorname{lcm}(1,\ldots,n),\qquad d_0=1,
 \quad T_{n,m}(t)=\frac{(n!)^s}{(m!)^2}S_{r,n,m}(t).
\]

Write its unique partial fractions as

\[
 T_{n,m}(t)=\sum_{j=0}^{n}\sum_{q=1}^{s}
                  \frac{c_{j,q}}{(t+j)^q}.
\]

Then, for every j,q in the indicated ranges,

\[
 \boxed{d_n^{s-q}c_{j,q}\in\mathbb Z.}
\]

In particular, if

\[
 \mathcal A_{n,m}=\sum_{k\ge1}T_{n,m}(k)
    =b_{n,m}+\sum_{\substack{3\le q\le s\\q\text{ odd}}}
                          a_{q,n,m}\zeta(q),
\]

then

\[
 d_n^{s-q}a_{q,n,m}\in\mathbb Z,\qquad d_n^s b_{n,m}\in\mathbb Z.
\]

Here is a proof for this specific kernel, so its denominator range is explicit.
First factor it as

\[
 T_{n,m}(t)=P_m(t)Q_n(t)^s,\quad
 P_m(t)=\binom{t-1}{m}\binom{t+n+m}{m},\quad
 Q_n(t)=\frac{n!}{\prod_{h=0}^n(t+h)}.
\]

For an integer a, Vandermonde's polynomial identity gives

\[
 \binom{a+x}{m}=\sum_{i=0}^m\binom{a}{m-i}\binom{x}{i}.
\]

All the coefficients binom(a,m-i) are integers, also for negative a, since
binom(-b,k)=(-1)^k binom(b+k-1,k) for b>0. For i>=1,

\[
 \binom{x}{i}=\frac{(-1)^{i-1}x}{i}
                     \prod_{h=1}^{i-1}(1-x/h).
\]

Every term contributing to its coefficient of x^l has a denominator equal
to a product of l integers from 1,...,i. Thus d_m^l times that coefficient
is integral. The same conclusion holds for every integer translate and,
by multiplying Taylor series, for P_m(-j+x). Since m<=n, d_n may replace d_m.

At the pole -j,

\[
 \bigl[xQ_n(-j+x)\bigr]^s
  =(-1)^{js}\binom nj^s
          \prod_{h\ne j}(1+x/(h-j))^{-s}.
\]

The coefficient of x^l in each factor is
(-1)^l binom(s+l-1,l)/(h-j)^l. Since 1<=|h-j|<=n,
d_n^l clears it. Products of these series retain the same weighted bound.
Now c_{j,q} is the coefficient of x^(s-q) in
P_m(-j+x)[xQ_n(-j+x)]^s, proving the boxed assertion.

For the zeta coefficients, sum c_{j,q} over j. Reflection cancels even q;
proper decay gives sum_j c_{j,1}=0. The rational constant is

\[
 b_{n,m}=-\sum_{j=0}^n\sum_{q=1}^s c_{j,q}H_j^{(q)}.
\]

Since d_n^q H_j^(q) is integral, d_n^s clears every summand of the constant.
For the simple-pole terms, subtract H_K*sum_j c_(j,1)=0 from the K-th
partial sum. The remaining upper boundary is bounded by a constant times
max_j (H_(K+j)-H_K)<=n/(K+1), which tends to zero. No value of zeta(1)
is used in the formula for b_(n,m).
This proves the claimed period-coefficient bounds without a prime number theorem.
For n=0 the products are empty and the same conclusion is immediate.

This proof is an explicit instance of the integral-valued-polynomial
arithmetic used in [Zudilin's hypergeometric arithmetic lemmas,
Section 2](https://www.numdam.org/item/JTNB_2004__16_1_251_0.pdf).
The bound is d_n, rather than the larger d_(n+m) obtained by treating all
individual numerator factors as unrelated rational terms.

The leading coefficient has the stronger exact expression

\[
 c_{j,s}=(-1)^{m+j}\binom nj^s
                    \binom{j+m}{m}\binom{n-j+m}{m}.
\]

The factorial-to-binomial magnitude identity and its integrality are
verified in `OddZeta/PadeArithmeticBudget.lean`. The identification of that
expression with the Laurent coefficient follows from the displayed pole
factorization in the paper proof.

## Exact prime accounting and primitive normalization

For each prime p,

\[
 v_p(\operatorname{den}c_{j,q})
       \le(s-q)\max\bigl(\{0\}\cup\{e\ge1:p^e\le n\}\bigr).
\]

For p>n the maximum is zero. This identifies the eligible prime powers;
it does not assert that each eligible power is necessary.

Take integer lower-period cancellation weights w_j for the blocks m=n-j,
0<=j<r. Set M=sum_j |w_j|. Let A,B be the integer coefficients of

\[
 J_n=d_n^s\sum_j w_j\mathcal A_{n,n-j}=A\zeta(s)+B,
 \qquad h=\gcd(|A|,|B|)>0.
\]

The primitive form is J_n/h, and the exact cost relative to the rational
combination normalized to sum of absolute weights one is

\[
 K_n=\frac{d_n^s M}{h},\qquad
 \left|\frac{J_n}{h}\right|
 \le K_n\max_j\mathcal A_{n,n-j}.
\]

The existing analytic rate theorem therefore reduces smallness to a genuine
estimate on K_n. For example, a strict inequality

\[
 \limsup_{n\to\infty,\ n\text{ even}}\frac{\log K_n}{n}
           <-\Phi_{s,1}(x_1)
\]

would suffice. This strict arithmetic inequality is not proved here.
Nonvanishing at arbitrarily large indices is also needed.

Changing the clearing factor alone cannot improve the primitive error:
replacing d_n^s by c*d_n^s multiplies A,B and h by c, so K_n is unchanged.
Lean verifies this invariance for every positive integer c. Thus the sharper
denominator theorem improves a bound that ignores h, but cannot manufacture
extra cancellation after the complete gcd has already been removed.

## A constructed rational telescoper

There is a useful exact application of the creative-telescoping proposal.
Let F(t) be any combined kernel after lower-period cancellation, with
partial fractions c_{j,q} and sum_j c_{j,q}=a when q=s and zero otherwise.
Define

\[
 \beta_{j,q}=\sum_{h=0}^j c_{h,q}-a\,\mathbf1_{q=s},\quad
 G(t)=\sum_{j=0}^{n-1}\sum_{q=1}^{s}\frac{\beta_{j,q}}{(t+j)^q}.
\]

Comparing the coefficient of every pole and pole order proves the identity

\[
 \boxed{F(t)=\frac{a}{t^s}+G(t)-G(t+1).}
\]

At the first pole the coefficient is a*1_(q=s)+beta_(0,q);
at an interior pole it is beta_(j,q)-beta_(j-1,q);
at the last it is -beta_(n-1,q). These are exactly c_(j,q).
Both sides are proper rational functions, completing the proof.
Consequently, since G(k) tends to zero,

\[
 \sum_{k\ge1}F(k)=a\zeta(s)+G(1).
\]

This explicitly identifies the rational constant with G(1). It is a
telescoper in the summation variable, not a new recurrence in n. Its existence
alone supplies no improved gcd estimate; it makes that estimate computable
from a specified rational function.

The actual block deformation also satisfies, identically,

\[
 S_{r,n,m+1}(t)=(t-m-1)(t+n+m+1)S_{r,n,m}(t).
\]

Lean verifies this for all parameters, including points where a denominator
is zero under Lean's total division convention.

## Nonvanishing and the limits of the ten proposals

For convergent positive-kernel sums, nonnegative rational weights, at least
one positive, give a strictly positive combined sum. This is now a general
Lean theorem for the actual kernels. The existence of such a nullvector for
all indices and all weights has not been proved.

| Proposal | What is established or still needed for these forms |
|---|---|
| 1. Saddle extraction | The individual positive sums have a rate theorem. A combined saddle proof needs a nonzero leading coefficient and a controlled remainder; moving a contour alone does not give that. |
| 2. Casoratians | An identified recurrence and a theorem about the selected component are needed. A nonzero Casoratian does not exclude infinitely many component zeros. |
| 3. Galois traces | The periods are not known to lie in a number field. Even in a number field, nonzero elements can have zero trace. |
| 4. p-adic valuations | The coefficient denominator budget above is explicit. A lower valuation bound does not exclude zero; a nonzero residue or finite upper valuation is required. Coefficient residues alone do not prove a real period pairing nonzero. |
| 5. Modular L-values | An actual modular object and an equality with its specified L-value must first be constructed, with that nonvanishing theorem's hypotheses checked. |
| 6. LCM refinements | Applied above with d_n, a prime-by-prime bound, and the exact full-gcd cost. Sharper clearing alone leaves the primitive form invariant. |
| 7. Mahler measures | Lower bounds do not supply the required upper coefficient bound. Sparse polynomials can have arbitrarily large Mahler measure. |
| 8. Creative telescoping | An explicit rational telescoper and block recurrence have been constructed. An arithmetic improvement from them still needs proof. |
| 9. Extension classes | A nontrivial extension does not itself quantify the integer coefficient cost or prove injectivity of the numerical period map on the required class. |
| 10. Interval certificates | Finite coefficient and gcd certificates are supplied. Covering all n>N_0 still requires a proved uniform tail theorem with explicit hypotheses. |

Three elementary checks illustrate why these hypotheses cannot be omitted.
The solutions of u_(n+2)=-u_n, v_(n+2)=-v_n with initial values (u_0,u_1)=(0,1),
(v_0,v_1)=(1,0) have Casoratian u_n*v_(n+1)-u_(n+1)*v_n=-1, but u_(2k)=0.
In Q(sqrt(2)), sqrt(2) has trace zero although it is nonzero and the field
discriminant is nonzero. Finally, v_p(0)=+infinity satisfies every lower
valuation bound. None is an obstruction to a better construction; each
identifies a missing inference in the corresponding proposed argument.

For motivic context, [Brown's theorem](https://annals.math.princeton.edu/2012/175-2/p10)
is a theorem about motivic multiple zeta values and their period images;
it is not an upper bound on the present K_n. No theorem asserting such a
bound is invoked in this development.

## Reproducible scope

`scripts/pade_arithmetic_budget.py` checks 236 even-index kernel cases at
weights 3,5,7,9 and indices 0,2,4,6,8,12,20, testing every m from 0 through n.
All 18,600 partial-fraction coefficient checks pass. It also checks 19 exact
combined-form ledgers at indices 2,4,8,12,20, omitting the profile m=n-j when
it would have a negative block length. All 19 have one-sign weights.
Their telescopers are certified at every pole coefficient, and the values
G(1) agree exactly with the rational constants. Larger common clearing
factors give exactly the same primitive costs in all 19 ledgers.

These finite calculations do not establish a limiting cost. For example,
the weight-five m=n,n-1 ledger has log(K_n)/n about 7.286432 at n=20,
while the analytic decay rate tends to about 4.970794 in absolute value.
This finite comparison is not an impossibility theorem or an asymptotic
estimate. The required strict limiting inequality remains open in this
construction.

Reproduce with Python 3.11 or newer and the standard library:

```text
python scripts/pade_arithmetic_budget.py --output pade-arithmetic-budget.json
```

The finite certificates are in `pade-arithmetic-budget.json`.

The five new Lean foundation reports are in
`lean-arithmetic-budget-verification.txt`; each uses only standard Lean
foundations. The complete Lean entry point compiled after the new import.
To reproduce the new Lean checks with the pinned toolchain:

```text
lake build
lake env lean scripts/AuditArithmeticBudget.lean
```

The three-page derivation is `pade-arithmetic-note.pdf`, with source
`pade-arithmetic-note.tex`. It compiled in both the desktop editor and
Tectonic. All three final rendered pages were inspected; the final log has
no overfull or underfull box warnings. Author and date fields are blank.
