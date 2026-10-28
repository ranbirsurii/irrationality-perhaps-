# An analytic extension to every large index

This derivation uses no finite-index audits. It gives an explicit
geometric upper bound for all three positive sums at every even n>=4,
and an explicit index after which the polynomial prefactor is absorbed.
It does not assume that the integer normalization cost is small.

Let n>=4 be even and 0<=m<=n. Define the positive summation kernel

\[
 T_{n,m}(t)=\frac{(n!)^5}{(m!)^2}
 \frac{\prod_{v=1}^{m}(t-v)(t+n+v)}
 {\prod_{h=0}^{n}(t+h)^5},\qquad
 A_{n,m}=\sum_{k=m+1}^{\infty}T_{n,m}(k).
\]

The series converges: the degree of the denominator minus the degree
of the numerator is 5n+5-2m>=3n+5. Set

\[
 S_n=\max_{j=0,1,2} A_{n,n-j}.
\]

The following bound is unconditional:

\[
 \boxed{S_n\le C_0(n+1)^{12}140^{-n},\qquad
 C_0=12\cdot3^{12}\cdot5^{10}e^{10}.}
 \tag{1}
\]

## A fixed-offset comparison with a uniform constant

Let 0<=j<=2, n>=4 and k>=n-j+1. The factorial formula gives

\[
 \frac{T_{n,n-j}(k)}{T_{n,n}(k+j)}
 =\left(\frac{n!}{(n-j)!}\right)^2
   \prod_{h=1}^j\left(\frac{k+n+h}{k+h-1}\right)^6
   \left(\prod_{h=1}^{2j}(k+2n-j+h)\right)^{-1}.
\]

Each ratio in the first product is at most three, because k>=n-1 and
1+(n+2)/(n-1)<=3. Each factor in the final product is at least 2n,
and n!/(n-j)!<=n^j. Consequently

\[
 T_{n,n-j}(k)\le\frac{3^{6j}}{4^j}T_{n,n}(k+j),\qquad
 A_{n,n-j}\le\frac{3^{6j}}{4^j}A_{n,n}.
 \tag{2}
\]

The shift maps the full summation range exactly onto k+j>=n+1, so
there are no omitted initial terms. In particular S_n<=3^12*A_(n,n).

## A global saddle bound by elementary calculus

Define for x>1

\[
 \Phi(x)=6[x\log x-(x+1)\log(x+1)]
       +(x+2)\log(x+2)-(x-1)\log(x-1).
\]

The derivative vanishes exactly when

\[
 x^6(x+2)=(x-1)(x+1)^6.
\]

Writing y=x(x+1), the difference between the right and left sides is
3y^3-4y^2-5y-1. For y>=2 its derivative 9y^2-8y-5 is positive,
while its value at two is -3. Thus there is exactly one stationary
point x_*>1. The derivative of Phi is positive before this point and
negative after it; this is its global maximum.

Put a=1057/1000. Exact integer arithmetic gives

\[
 1000^6[3(a(a+1))^3-4(a(a+1))^2-5a(a+1)-1]
 =54685013669880747>0.
\]

Hence 1<x_*<a. At the stationary point, multiplying the derivative
identity by x_* cancels the terms with coefficient x_*, leaving

\[
 \Phi(x_*)=\log q(x_*),\qquad
 q(x)=\frac{(x+2)^2(x-1)}{(x+1)^6}.
\]

For 1<x<=a,

\[
 (\log q)'=\frac2{x+2}+\frac1{x-1}-\frac6{x+1}
             >\frac{1000}{57}-3>0.
\]

Finally q(a)<1/140 is the integer inequality

\[
 2057^6-140\cdot3057^2\cdot57\cdot1000^3
 =1178944474661131249>0.
\]

Therefore the following holds for every real x>1:

\[
 \boxed{\Phi(x)\le\Phi(x_*)<-\log140.}
 \tag{3}
\]

These calculations bound a single global maximum; they are not an
extrapolation from sampled indices or a numerical asymptotic hypothesis.

## Uniform tail control

For m=n put E=3n+3 and B=7n^2+5n, and choose

\[
 K=\max\{2n,n+1,\lceil B/E\rceil\}\le3n.
\]

Logarithmic differentiation of the rational kernel gives, for t>=2n,

\[
 \frac{d}{dt}\log(t^2T_{n,n}(t))
       \le-\frac E t+\frac B{t^2}.
\]

For example, use 1/(t-v)<=1/t+2v/t^2, 1/(t+n+v)<=1/t, and
1/(t+h)>=1/t-h/t^2 in the three finite sums of derivatives.
The stated B is a valid upper bound on the resulting second-order term.
For t>=K the derivative is nonpositive. Thus

\[
 T_{n,n}(k)\le T_{n,n}(K)(K/k)^2\quad(k\ge K).
\]

The maximum summand P_n is consequently attained between n+1 and K.
The integral bound on the sum of k^(-2) then proves

\[
 A_{n,n}\le(2K+1)P_n\le(6n+1)P_n.
 \tag{4}
\]

## An explicit polynomial prefactor

Let f(u)=u*log(u)-u for u>0 and f(0)=0. Integral comparison proves,
for every integer r>=0,

\[
 f(r)\le\log(r!)\le f(r)+1+\log(r+1).
\]

At a maximizing summation index n+1<=k<=3n the exact kernel is

\[
 T_{n,n}(k)=
 \frac{(n!)^3((k-1)!)^6(k+2n)!}
 {(k-n-1)!((k+n)!)^6}.
\]

Applying the upper factorial error to the ten numerator factors and
the lower error to the denominator factors bounds its logarithm by

\[
 3f(n)+6f(k-1)+f(k+2n)-f(k-n-1)-6f(k+n)
                  +10[1+\log(5n+1)].
\]

Replacing k-1 by k and k-n-1 by k-n in the main expression changes it
by at most log(2n). Indeed f(k-1)-f(k)<=0, while
f(k-n)-f(k-n-1)<=log(k-n)<=log(2n), including k-n=1.
The resulting expression is exactly n*Phi(k/n). Equations (3)-(4) give

\[
 A_{n,n}\le 2e^{10}n(6n+1)(5n+1)^{10}140^{-n}.
\]

Combining this with (2), and bounding n<=n+1, 6n+1<=6(n+1), and
5n+1<=5(n+1), proves (1).

## A completely explicit large-index exponential bound

The elementary inequality log(1+n)<=sqrt(n) holds for n>=1: the
derivative of sqrt(x)-log(1+x) is nonnegative and its value at zero
is zero. Also C_0<e^70, using e>2 and the displayed integer factors.
For every n>=5760000,

\[
 \log C_0+12\log(n+1)\le70+12\sqrt n\le n/100.
\]

It follows, for every even n>=5760000, that

\[
 \boxed{S_n\le e^{-(\log140-0.01)n}<e^{-4.93n}.}
 \tag{5}
\]

For the final numerical comparison one can avoid decimal logarithms:
the positive series for log(2) gives log(2)>693/1000, and
log(35/32)>6/67. Hence
log(140)=7log(2)+log(35/32)>4.94.

## What this proves for the integer linear forms

For every selected nonzero nonnegative integer cancellation vector
w=(w_0,w_1,w_2), let M_n=sum_j w_j. Write the cleared form as
d_n^5*sum_j w_j A_(n,n-j)=a_n*zeta(5)+b_n with integer a_n,b_n,
let h_n=gcd(abs(a_n),abs(b_n)), and define L_n to be this cleared
form divided by h_n. Positivity ensures h_n>0. The existing algebra gives

\[
 0<L_n\le K_n S_n,\qquad K_n=d_n^5M_n/h_n.
\]

Consequently (1) proves the unconditional large-index upper bound

\[
 \boxed{0<L_n\le C_0(n+1)^{12}K_n140^{-n}.}
 \tag{6}
\]

If one proves K_n<=exp(4.92*n) at arbitrarily large indices, then (5)
gives L_n<exp(-n/100) at those indices above the explicit cutoff. The
usual integer-smallness contradiction would then prove irrationality.
This is a sufficient arithmetic condition, not an established estimate
for K_n.

Analytic decay before integer normalization cannot replace that condition.
For instance f_n=2^(-n)*xi tends to zero for any positive rational xi,
but primitive normalization of its rational coefficient pair (2^(-n),0)
gives the constant form xi. This example is not the present kernel; it
shows why an unproved normalization estimate cannot be removed from
the argument by retaining only analytic decay.

Thus the analytic extension to all large indices is proved explicitly.
The required arithmetic bound on K_n remains unproved. These derivations
do not conclude the irrationality of zeta(5), or of every odd zeta value,
and are not presented as a completed Lean theorem. No finite-index
audits, further compilation, or arXiv submission were performed here.
