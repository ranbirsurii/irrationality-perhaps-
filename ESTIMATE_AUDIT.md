# Joint arithmetic and analytic estimate audit

The quantity to minimize is the size of the **primitive integer linear form**,
after clearing denominators and dividing out the common integer gcd. Smallness
of a rational form and cheap coefficients for a formal weight projector do not
separately settle this calculation.

For `a_n zeta(5) + b_n`, with `a_n` integral and `b_n` rational, put

\[
d_n=\operatorname{den}(b_n),\qquad
g_n=\gcd(|d_na_n|,|d_nb_n|),\qquad
\Lambda_n=\frac{d_n}{g_n}(a_n\zeta(5)+b_n).
\]

The relevant exponential budget is
\[
-\frac1n\log|a_n\zeta(5)+b_n|
-\frac1n\log(d_n/g_n).
\]
It must eventually be positive, with nonzero forms, for the usual exponential
integer-smallness argument. Polynomial decay can also suffice if the full
normalization cost permits it. No exponential slope is assumed in this audit.

## 1. The displayed Adams-coordinate form has the wrong sign and growth

Here all symbols `A_n, B_n, C_n, E_n` mean the finite rational formulas in
`AperyFive.lean`. The displayed projected form is
\[
F_n=-4A_n\zeta(5)-\frac7{24}E_n.
\]

The finite coefficient formulas give the following limits:
\[
\frac{B_n}{A_n}\longrightarrow2\zeta(3),\qquad
\frac{C_n}{A_n}\longrightarrow-8\zeta(2),\qquad
\frac{E_n}{A_n}\longrightarrow4\zeta(5)+8\zeta(2)\zeta(3).
\tag{1}
\]
These statements concern finite harmonic sums. Their derivation does not assume
the infinite-series interpretation of `L_1`, or any irrationality statement.

Here is a proof of the limits, including control of the tails. Set
\[
w_{n,k}=\binom nk^2\binom{n+k}k^2,\quad
p_{n,k}=w_{n,k}/A_n,\quad c=1/\sqrt2.
\]
The exact consecutive-weight identity is
\[
\frac{w_{n,k+1}}{w_{n,k}}
=\left(\frac{(n-k)(n+k+1)}{(k+1)^2}\right)^2
\quad(0\le k<n).
\tag{2}
\]
Its limiting ratio at `k/n=x>0` is `((1-x^2)/x^2)^2`, strictly larger than one
to the left of `c`, and strictly smaller than one to its right.

Fix `0<epsilon<min(c,1-c)`. Comparing the weights at `c-epsilon` with those
at `c-epsilon/2`, and similarly on the right, gives constants `K_epsilon>0`,
`0<q_epsilon<1` and `N_epsilon` such that
\[
\sum_{|k/n-c|\ge\epsilon}p_{n,k}
\le K_\epsilon(n+1)q_\epsilon^n\quad(n\ge N_\epsilon).
\tag{3}
\]
For completeness these constants can be chosen directly from (2). Put
`a=c-epsilon/2`, `b=c+epsilon/2`,
`L=(1+((1-a^2)/a^2)^2)/2>1`, and
`Q=(1+((1-b^2)/b^2)^2)/2<1`. For all sufficiently large `n`, the ratio in
(2) is at least `L` whenever `k/n<=a`, and at most `Q` whenever `k/n>=b`.
Indeed its unsquared numerator is `1-x^2+(1-x)/n` and its denominator is
`(x+1/n)^2`; use the bounds `1-a^2`, `(a+1/n)^2` on the left and
`1-b^2+1/n`, `b^2` on the right. At least `epsilon*n/2-O(1)` consecutive
ratios separate either tail from the intervening comparison index. Each tail
weight is therefore at most `A_n` times the corresponding geometric factor;
summing at most `n+1` weights proves (3).

On every fixed closed interval around `c` contained in `(0,1)`, uniformly in
`k/n=x`,
\[
\eta_{n,k}=\log\frac{1-x^2}{x^2}+O(1/n),\qquad
H^{(s)}_{n+k},H^{(s)}_k,H^{(s)}_{n-k}\longrightarrow\zeta(s)\quad(s>1).
\tag{4}
\]
Use `H_N=log N+gamma+O(1/N)` and the convergent positive `s`-series. Every
local factor defining `B_n`, `C_n`, and `E_n` is bounded in absolute value by
`K(1+log(n+1))^3`, uniformly over **all** `k`. This follows from
`H_N<=1+log N` and boundedness of `H_N^(s)` for `s>=2`. Thus (3) makes the
contribution from outside the fixed interval tend to zero. Inside it, (4)
reduces the weighted average to a continuous function of `x`; shrinking the
interval to `c` evaluates it at `eta=0`.

For the `E` calculation, write its local factor as
\[
e=4H_k^{(5)}-6\eta H_k^{(4)}
 +2(u_0+v_0)H_k^{(3)}+(u_1-2\eta v_0+v_1)H_k^{(2)},
\]
where `u_0,u_1,v_0,v_1` are precisely the regular/pole expressions in the
Lean definitions. At `x=c`, they tend to `2 zeta(2),0,2 zeta(2),0`, respectively.
This proves the last limit of (1). The other two follow from their displayed
local factors in the same weighted-average argument.

Consequently
\[
\boxed{\frac{F_n}{A_n}\longrightarrow
-\frac{31}{6}\zeta(5)-\frac73\zeta(2)\zeta(3)<0.}
\tag{5}
\]
In particular `E_n>0` eventually. Once `E_n>=0`, `A_n>=1` gives
`|F_n|>=4 zeta(5)`. Even arbitrary denominator cancellation cannot rescue this
form: after a nonzero rational scaling to integer coefficients and a sign
change, it is `a zeta(5)+b` with integers `a>=1`, `b>=0`. Its absolute value is
at least `zeta(5)>1`.

The growth exponent can also be computed. Stirling's factorial bounds, uniform
in `0<=k<=n`, give
\[
\log w_{n,k}=n\Phi(k/n)+O(\log(n+1)),\quad
\Phi(x)=2\big((1+x)\log(1+x)-(1-x)\log(1-x)-2x\log x\big).
\]
The maximum is uniquely at `c`, where `Phi(c)=4 log(1+sqrt(2))`. Bounding the
sum by `(n+1)` times its largest summand gives
\[
\frac1n\log A_n\to\log(17+12\sqrt2),\qquad
\frac1n\log|F_n|\to\log(17+12\sqrt2)>0.
\tag{6}
\]

Formalization scope: `AperyEstimateAudit.lean` proves (2) in cleared form,
`A_n>=1`, the exact weighted-local identity for `E_n`, the local evaluation
used in (1), and the sign/normalization inequalities. The concentration and
asymptotic arguments (3)--(6) above are mathematical proofs in prose; they have
not yet been translated into Lean. No Lean theorem asserting those limits is
claimed.

## 2. A concrete alternative projector and its cost

Positive half-integer summation has the distribution identity
\[
\sum_{j\ge0}(j+\tfrac12)^{-s}=(2^s-1)\zeta(s)\quad(s>1).
\]
Thus integer and half-integer evaluations of the first deformed partial
fractions have coefficients
\[
L=-4A_n\zeta(5)+C_n\zeta(3)+E_n,
\quad L^{1/2}=-124A_n\zeta(5)+7C_n\zeta(3)+E_n^{1/2}.
\]
The difference `L^(1/2)-7L` is
`-96A_n zeta(5)+E_n^(1/2)-7E_n`. The rational correction is computed by replacing
`H_k^(s)` in the rational-part formula with
`2^s sum_(j=0)^(k-1) 1/(2j+1)^s`. It is **not** the displayed Adams rational
correction. Removing the half-grid terms below `n` preserves the zeta
coefficients and changes the rational term by an explicit finite sum.

The script `scripts/joint_estimate_audit.py` computes these rational
coefficients exactly, clears their reduced denominators, removes their full
common gcd, and encloses each resulting pure zeta-five form in a rational
interval. This audits the candidate coefficient formulas; a general shifted
partial-fraction/series identity is not yet a theorem in the Lean project.

For `n=40`, define the finite-index exponent to be `-log(abs(form))/n`.

| Candidate | Rational-form exponent | Primitive-integer-form exponent |
| --- | ---: | ---: |
| Displayed Adams-coordinate form | -3.406334 | -7.837077 |
| Scalar elimination | 0.239699 | -4.137333 |
| Full half-grid cancellation | 0.063746 | -7.375168 |
| Half-grid tail cancellation | 3.221943 | -15.958558 |

Negative values mean growth. The decisions `abs(primitive form)>1` are exact
rational-interval comparisons, not floating-point tests. The logarithms are
only displays. Results at a finite list of indices do not establish the
asymptotic behavior of the last three candidates.

The enclosure of `zeta(5)` uses 600 Euler-transform terms. If
`d_k=sum_(j=0)^k (-1)^j binom(k,j)/(j+1)^5`, then
\[
d_k=\frac1{24}\int_0^1(-\log x)^4(1-x)^k\,dx,\quad0<d_k\le1,
\]
and `eta(5)=sum_(k>=0) 2^(-k-1)d_k`. Hence the omitted tail is between zero
and `2^-600`; divide by `1-2^-4` to enclose `zeta(5)`. The code uses exact
fractions throughout this computation.

## 3. Best remaining direction and less standard alternatives

The displayed Adams-coordinate form is ruled out by its sign. The strongest
concrete replacement to investigate is a **new sampling-compatible kernel**
whose numerator zeros cover every sampling lattice before the period is taken,
combined with prime-by-prime denominator optimization. The current half-grid
tail has a large arithmetic cost, so adding the half-grid projector after
constructing the old kernel is insufficient evidence for a positive budget.

A first such replacement has now been constructed explicitly:
\[
K_n(t)=n!(2t+n)
\frac{\prod_{j=1}^{2n}(t-j/2)(t+n+j/2)}
     {\prod_{j=0}^{n}(t+j)^5}.
\tag{7}
\]
Its numerator vanishes at **both** positive sampling lattices through `n`.
Lean proves those zeros and the numerator reflection identity. For odd `n`,
reflection of the whole rational function is odd; pairing its poles therefore
leaves only odd zeta coefficients in a direct sum. This parity observation and
the infinite-series evaluation of (7) are not yet formalized in Lean.

The analytic budget of this replacement can already be tested exactly. At
`t=nx`, `x>1`, its Stirling phase is
\[
\Phi_2(x)=7x\log x-2(x-1)\log(x-1)
 +2(x+2)\log(x+2)-7(x+1)\log(x+1).
\]
The stationary equation is
\[
x^7(x+2)^2=(x-1)^2(x+1)^7,
\]
equivalently
`x^8+4x^7-14x^5-14x^4+8x^2+5x+1=0`; Lean checks this polynomial identity.
There is a unique root above one, approximately `1.8426653079611632`, giving
raw decay exponent approximately `2.2709006892715973`. Indeed
`Phi_2''(x)=(x^2+x-14)/(x(x+1)(x-1)(x+2))`; the first derivative decreases
and then increases to zero from below, so it crosses zero just once.

Multiplying (7) by `2^(4n)` clears the powers of two displayed in its numerator,
although additional cancellation could make the primitive normalization
smaller. This normalization already loses decay. An exact one-point witness is
\[
2^{4n}K_n(2n)=
\frac{5n\,n!\,(4n-1)!\,(8n)!\,(2n-1)!^4}{(6n)!\,((3n)!)^5},
\]
whose logarithmic growth exponent is
\[
34\log2-21\log3>0,
\quad\text{since }2^{34}>3^{21}.
\tag{8}
\]
Lean verifies the strict positivity in (8); the factorial asymptotic is a
Stirling calculation in this note. For the complete sampled sums, the same
nondegenerate saddle has width of order `sqrt(n)`, so integer and half-integer
sampling have the same leading Laplace term. Their combination with
coefficients `1,-7` has leading multiplier `-6`, rather than cancelling that
term. Thus a successful variant needs a substantial arithmetic improvement or
a different kernel/saddle cancellation; the naive normalization is inadequate.

The alternatives considered jointly with their unresolved obligations are:

| Route | What it could improve | Required calculation |
| --- | --- | --- |
| Sampling-compatible kernel and factorial symmetries | Both decay and denominator cancellation | Build the new kernel, then optimize the saddle exponent minus the exact prime-valuation cost. |
| Lattice reduction of primitive pairs | Common integer factors | Already included in the finite audit; it does not fix the displayed form's sign. |
| Determinants of adjacent forms | Cancellation of dominant saddles | Prove the determinant remains a linear form in the chosen zeta value and control its full height and nonvanishing. |
| Multiple orthogonality and Hermite--Padé approximation | Joint nonvanishing and saddle control | Construct positive measures or contour systems realizing the same target coefficient lattice. |
| Moving deformation radius with `n` | A different analytic optimization | Track the Cauchy coefficient-extraction factor and all newly introduced denominators at the same time. |
| Prime-local factorial cancellation | Smaller arithmetic exponent | Derive an exact floor-function formula for every prime valuation; numerical gcds alone are insufficient. |
| Finite group actions on cellular periods | Many arithmetic symmetries at once | Identify this construction's actual integral lattices and period relations under the action. |
| Overconvergent or p-adic methods | A different smallness mechanism | Establish an explicit relation to the **real** zeta target; p-adic irrationality does not imply the real claim. |

Recent primary examples motivate two of these directions. Brown--Zudilin's
[cellular-integral construction](https://arxiv.org/abs/2210.03391v3) uses a large
symmetry group to obtain effective zeta-five rational approximations with
exponent `0.86`; that is below the exponent `>1` that by itself contradicts
rationality for unbounded denominators. Lai--Sprang--Zudilin's
[2-adic zeta-five work](https://arxiv.org/abs/2505.05005v2) gives an actual
irrationality theorem for a different, 2-adic target. These are methodological
comparisons, not imported proofs of the real all-odd claim.

No candidate examined here establishes the full irrationality theorem. The
displayed projection's failed decay is a proved sign/growth issue, and the
remaining candidates require a new joint estimate with a positive budget.

## 4. A stronger structural alternative: pure-target moment determinants

The most useful alternative found in this audit isolates the target and gives
nonvanishing before any weight projection. For `s=5`, let
\[
\mu_k=\zeta(5)-H_k^{(5)}
=\frac1{24}\int_0^1\frac{x^k(-\log x)^4}{1-x}\,dx,
\quad
\Delta_{N,a}=\det[\mu_{a+i+j}]_{0\le i,j<N}.
\tag{9}
\]
Expand `1/(1-x)` into its nonnegative geometric series and integrate termwise
to prove the moment identity. The measure in (9) is finite and strictly
positive on `(0,1)`. The Gram determinant formula gives
\[
\Delta_{N,a}=\frac1{N!}\int_{(0,1)^N}
 \prod_{i<j}(x_i-x_j)^2\prod_i
 \frac{x_i^a(-\log x_i)^4}{24(1-x_i)}\,dx_1\cdots dx_N>0.
\tag{10}
\]
The integral is finite because it is bounded by a finite sum of products of
finite moments; it is strictly positive on any product of disjoint interior
intervals. This proves nonvanishing for every `N>=1` and `a>=0`.

Each matrix in (9) is `zeta(5) J - H`, where `J` is the rank-one all-ones
matrix and `H` is rational. Multilinearity, or subtracting the first row from
all other rows, gives **exactly**
\[
\Delta_{N,a}=A_{N,a}\zeta(5)+B_{N,a},\qquad A_{N,a},B_{N,a}\in\mathbb Q.
\tag{11}
\]
`AperyHankel.lean` proves the generic affine determinant identity over any
commutative ring, and its rational-coefficient and real specializations for
these harmonic matrices. It does not yet formalize (9)--(10).

The leading coefficient also has the exact rational determinant expression
\[
A_{N,a}=\det\left[
\frac1{(a+i+j+1)^5}-\frac1{(a+i+j+2)^5}
\right]_{0\le i,j<N-1}>0.
\tag{12}
\]
To derive it, use the integer unimodular polynomial basis
`1,(1-x),x(1-x),...,x^(N-2)(1-x)`. Only the first basis function is nonzero
at `x=1`, so the zeta coefficient of the transformed moment matrix is confined
to its top-left entry; the lower principal block consists of the moments of
`(1-x)^2` times the original measure. Those moments are the rational
differences in (12). Positivity follows by the same Gram argument.
The script checks (12) against two independent rational determinant
evaluations, in addition to performing the interval audit.

This route handles target isolation and nonvanishing. Its baseline arithmetic
cost is still too large in the finite tests. Since determinant sizes naturally
operate on an `N^2` scale, the following exponents are divided by `N^2`:

| `N=20`, moment shift `a` | Raw determinant decay exponent | Primitive integer decay exponent |
| --- | ---: | ---: |
| 0 | 1.517981 | -4.772732 |
| 20 | 2.437881 | -7.891856 |
| 40 | 2.923034 | -9.709984 |
| 60 | 3.260941 | -10.955639 |
| 80 | 3.521115 | -11.994359 |

These entries are certified finite comparisons, not asymptotic theorems.
The simple shift improves analytic smallness but worsens the combined budget
at the tested indices. A rational change of basis within the **same**
polynomial space cannot fix the primitive form: it multiplies the determinant
by the rational scalar `(det T)^2`, leaving the primitive integer pair unchanged
up to sign. A genuine improvement must change the polynomial subspace, moment
weight, or arithmetic identities, and then recompute the exact primitive pair.

This is the preferred structural branch after the failed displayed projector:
seek such a modified moment construction while optimizing its exact prime
valuations and its determinant/saddle decay together. The original Hankel
family and the tested shifts do not establish a positive budget. The same
moment construction exists for other integer `s>1`, with
`(-log x)^(s-1)/(s-1)!` in place of `(-log x)^4/24`; that does not by itself
supply irrationality at any new target.
