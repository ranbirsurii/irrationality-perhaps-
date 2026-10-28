# Arithmetic audit before further compilation

The winning arithmetic bound is not proved. No further Lean or TeX
compilation was performed after the request to establish that bound first.
The existing global-sign PDF and Lean verification reports concern the
sign/nonvanishing result, with the scope stated in that note. They are not
certificates of an irrationality proof.

## The multiplier, independently normalized

For the two normalized weight-five blocks with lengths n and n-1, let
their rational period coordinates be (alpha_i,a_i,b_i), i=0,1. The global
sign theorem gives alpha_0*alpha_1<0 for every even n>=2. Choose relatively
prime positive integer weights w_0,w_1 with

\[
 w_0\alpha_0+w_1\alpha_1=0,\quad M=w_0+w_1,\quad D=d_n^5.
\]

The denominator theorem proves integrality of

\[
 A=D(w_0a_0+w_1a_1),\quad B=D(w_0b_0+w_1b_1).
\]

Their pair is nonzero by the positive-sum argument. Put h=gcd(|A|,|B|)>0.
For the rational coefficient pair normalized to mass one,

\[
 (\widehat a,\widehat b)=
 \frac{(w_0a_0+w_1a_1,w_0b_0+w_1b_1)}{M},
\]

the exact primitive multiplier is

\[
 K=DM/h,\qquad K(\widehat a,\widehat b)=(A/h,B/h).
\]

Independently, let delta be the least common denominator of the two
coordinates (a_hat,b_hat), and let c be the gcd of the integer pair
delta*(a_hat,b_hat). Then

\[
 \boxed{K=\delta/c.}
\]

Indeed both constructions multiply the same nonzero rational vector by a
positive scalar to obtain a relatively prime integer pair. Two such pairs
on the same positive rational ray coincide: their proportionality factor
has denominator dividing both coordinates, hence is an integer; reversing
the roles proves its reciprocal is an integer too. Thus the factor is one.
This also verifies that excess denominator clearing cannot change K.

## Independent coefficient calculations

`scripts/audit_primitive_normalization.py` computes the full weight-five
Laurent jets by logarithmic differentiation. If L_j is the signed leading
binomial coefficient and h_s(k)=sum_(v=1..k) v^(-s), set

\[
 t_s=(-1)^{s-1}\{(-1)^s h_s(j+m)+h_s(n-j+m)
                   -6[(-1)^s h_s(j)+h_s(n-j)]\}.
\]

The Taylor coefficients obey e_0=1 and
e_u=(sum_(s=1..u) t_s e_(u-s))/u for 1<=u<=4. This follows by
differentiating the exponential of the logarithmic Taylor series.
The pole coefficients are c_(j,q)=L_j*e_(5-q). The script checks the
denominator bounds, reflection cancellations and the complete rational
constant -sum_(j,q)c_(j,q)h_q(j).

At n=2,4,8,12,20 it compares these coordinates exactly with the earlier
independent calculation that multiplies truncated rational Taylor series
factor by factor. At all eight listed indices it compares both primitive
normalizations, including both primitive integer coordinates. All agree.

## Exact positive lower bounds, and their limited scope

The first nonzero term of each positive kernel sum is

\[
 T_{n,m}(m+1)=
 \frac{(n!)^5(m!)^4(n+2m+1)!}{((n+m+1)!)^6}>0.
\]

Consequently the actual primitive form satisfies the rigorous lower bound

\[
 \frac{A\zeta(5)+B}{h}
 =K\frac{w_0\mathcal A_{n,n}+w_1\mathcal A_{n,n-1}}M
 \ge K\min_{m\in\{n,n-1\}} T_{n,m}(m+1).
\]

The script checks this last rational lower bound against one using exact
integer arithmetic. It exceeds one at n=8,12,20,40,80,160. No numerical
evaluation of a zeta value is used in that conclusion.

Approximate log rates below summarize rigorous rational enclosures in
`primitive-normalization-audit.json`:

| n | log(K)/n | log(h/M)/n | Proved primitive lower bound > 1 |
|---:|---:|---:|:---:|
| 2 | 5.654596 | -3.921728 | No |
| 4 | 5.563942 | -2.457809 | No |
| 8 | 6.391977 | -2.183601 | Yes |
| 12 | 6.417520 | -2.155058 | Yes |
| 20 | 7.286432 | -2.470018 | Yes |
| 40 | 7.089003 | -2.562184 | Yes |
| 80 | 7.565173 | -2.598641 | Yes |
| 160 | 7.553433 | -2.655354 | Yes |

"No" means this particular lower bound does not exceed one; it is not
an upper bound on the form. These finite data prove neither an eventual
growth rate nor impossibility of a successful sequence or another family.

## Why the analytic estimate alone does not finish the argument

Since both normalized weights are positive,

\[
 \min(\mathcal A_{n,n},\mathcal A_{n,n-1})
 \le \frac{w_0\mathcal A_{n,n}+w_1\mathcal A_{n,n-1}}M
 \le \max(\mathcal A_{n,n},\mathcal A_{n,n-1}).
\]

Both outside sequences have logarithmic rate lambda_5 in
(-4.970794,-4.970793), by the positive-sum saddle estimate with fixed
offsets. Squeezing their logarithms therefore gives

\[
 \frac1n\log\left|\frac{A\zeta(5)+B}{h}\right|
       =\frac{\log K_n}{n}+\lambda_5+o(1).
\]

There is no cancellation between these two evaluated positive sums.
Rearranging their separate expansions cannot by itself improve this
exponential rate. A different family with signed combinations would
require its own decay and nonvanishing argument.

A strict upper bound limsup log(K_n)/n < -lambda_5 suffices for smallness.
A strict lower bound liminf log(K_n)/n > -lambda_5 would rule out smallness
for this particular full sequence. Neither asymptotic inequality follows
from the finite table. Using log(d_n)/n -> 1, the sufficient inequality is
the gcd-to-mass estimate in `arithmetic-twists-comparison.md`:

\[
 \liminf_{n\to\infty,\ n\text{ even}}
 \frac{\log h_n-\log M_n}{n}>5+\lambda_5.
\]

That is the remaining unproved arithmetic statement, not an assumption
that can be suppressed when compiling or publishing the proof.
