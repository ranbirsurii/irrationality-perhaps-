# A proved lower-column divisor and the remaining image-content problem

This note proves a uniform arithmetic gain for the lower-period row of
the three-block construction. Its proof uses a finite-field translation
trace and an explicit first-order congruence. It does not prove the
required growth of the image content Gamma_n. A proposed stronger
pointwise bound for that content has an exact counterexample below.
No new Lean or TeX compilation was performed; this is a paper proof
supported by reproducible exact checks.

## Coefficients and the proved divisor

For the same factorial-normalized rational kernel T_(n,m), write
c_(j,k) for its Laurent coefficients and define

\[
 a_k(n,m)=\sum_{j=0}^n c_{j,k},\qquad
 b(n,m)=-\sum_{j=0}^n\sum_{k=1}^5c_{j,k}H_j^{(k)}.
\]

These definitions also make sense for odd n. In that case the raw kernel
here has no additional factor (2t+n); its odd coefficient sums vanish by
reflection. The even-period coefficients are not being omitted from an
asserted period decomposition for odd n.

For even n>=6, set D=d_n^5,
x_i=D*a_3(n,n-i), i=0,1,2, and g_n=gcd(x_0,x_1,x_2). Put

\[
 B_n=n(n-1)(n-2)\prod_{j=0}^{12}(3n-j),\qquad
 c_{n,p}=\left\lfloor\frac{3n}{2p}\right\rfloor
                 -3\left\lfloor\frac n{2p}\right\rfloor.
\]

Then the following explicit integer divides g_n:

\[
 \boxed{
 G_n=d_n^3
 \prod_{n<p\le3n/2}p
 \prod_{\substack{p\le n,\ p^2>3n+6,\ p\nmid B_n\\c_{n,p}>0}}p
 \quad\mid\quad g_n.}
 \tag{1}
\]

All products are over primes. The boundary exclusions are deliberately
larger than necessary, so the endpoint cases have no hidden assumptions.

## Translation trace for primes above n

Let p>n and p>5. The denominator theorem makes every Laurent coefficient
p-integral. Reduce the kernel modulo p and put F(t)=t^p-t. Its denominator
divides F(t)^5, so

\[
 P(t)=F(t)^5\overline{T}_{n,m}(t)\in\mathbb F_p[t],\qquad
 \deg P\le5p+2m-5n-5.
\]

For any polynomial P, the trace Tr(P)=sum_(a in F_p)P(t+a) has degree
at most deg(P)-(p-1), unless it is zero. Expand each monomial and use
sum_a a^h=0 for 0<=h<p-1, including h=0 in characteristic p.
Also F(t+a)=F(t), and for 1<=k<=5,

\[
 \sum_{a\in\mathbb F_p}(t-a)^{-k}=(-1)^k F(t)^{-k}.
\]

The last identity follows from F'/F=-1/F and repeated differentiation;
the required integers 1,...,4 are invertible modulo p. Applying it to
the reduced partial fractions gives

\[
 \operatorname{Tr}(P)=\sum_{k=1}^5(-1)^k\overline{a_k(n,m)}F^{5-k}.
\]

If n<p<=3n/2 and 0<=m<=n, the degree bound is

\[
 \deg\operatorname{Tr}(P)\le4p+2m-5n-4<2p.
\]

The displayed polynomial has no F^2 term, since its powers have distinct
degrees. Thus a_3(n,m)=0 modulo p. This proves the middle prime product
in (1) for every block, not just the three selected lengths.

## A first-order congruence for the three-coordinate matrix

Let p>5 with p^2>3n+6, and write n=pq+r and m=pq+s, with
0<=s<=r<p. Define A_5(r,s)=a_5(r,s), an integer, and use the same raw
kernel at q, even when q is odd. In the p-integral coefficient ring,

\[
 \boxed{
 (p^2a_3(n,m),\ a_5(n,m),\ p^5b(n,m))
 \equiv A_5(r,s)(a_3(q,q),\ a_5(q,q),\ b(q,q))\pmod p.}
 \tag{2}
\]

Here is a product-level derivation. Split a complete set of residue
representatives as 0<=a<p and examine p^5*T_(n,m)(pX-a). Factor out
all multiples of p in its numerator and denominator. Wilson's identity
for each complete nonzero residue block gives

\[
 (pq+r)!/p^q\equiv(-1)^q q!r!\pmod p,
\]

and similarly with s. The condition on p ensures all factorial arguments
used in this calculation are below p^2. For a<=r, the factors with
denominator divisible by p give product_(j=0..q)(X+j)^5. If neither
numerator residual interval crosses p, the divisible numerator factors
are product_(j=1..q)(X-j)(X+q+j). The remaining unit factor is

\[
 (q!)^3(-1)^{s+a}
 \frac{(r!)^5(a+s)!(r-a+s)!}
 {(s!)^2(a!)^6((r-a)!)^6}.
\]

After including the factor (q!)^3 in T_(q,q), the other factor is
exactly c_(a,5) for the small kernel T_(r,s). If a numerator interval
crosses p, the reduction is zero and this same c_(a,5) is divisible by p.
For a>r the whole reduction is zero: the denominator has only q complete
p-factors and the residual p-valuation is at least five. Consequently

\[
 p^5\sum_{a=0}^{p-1}T_{n,m}(pX-a)
       \equiv A_5(r,s)T_{q,q}(X)\pmod p.
 \tag{3}
\]

To read the first two coordinates rigorously, separate the principal
parts at the integer poles of the left side. Every original pole j has
exactly one representative a congruent to j modulo p. Its k-th Laurent
coefficient becomes p^(5-k)*c_(j,k), which is p-integral by the uniform
denominator theorem. The integer poles 0,-1,...,-q remain distinct
modulo p. All other poles have p-adic absolute value greater than one;
their terms have coefficients divisible by p when expanded over the
integral disk, and reduce to zero. Taking the third- and fifth-order
coefficient sums in (3) therefore gives the first two coordinates in (2).

For the rational coordinate, use the finite identity

\[
 H_j^{(k)}=p^{-k}H_{\lfloor j/p\rfloor}^{(k)}+U_{j,k},
 \qquad U_{j,k}\in\mathbb Z_{(p)}.
\]

The contribution p^5*c_(j,k)*U_(j,k) is divisible by p, since its
valuation is at least k>=1. The remaining harmonic sums are precisely
the rational boundary coordinate of the integer principal parts in (3).
This proves the third coordinate of (2). No p-adic evaluation of the
infinite series at its convergence boundary is used.

## Carry cases and proof of (1)

The baseline d_n^3 | x_i follows from d_n^2*a_3(n,n-i) being integral.
For a prime in the last product of (1), p does not divide n(n-1)(n-2),
so r>=3 and all three m=n-i have the same quotient q, with s=r-i.
For p<=n the baseline valuation of x_i is at least three.

If q is odd, reflection of the raw small kernel gives a_3(q,q)=0.
Thus (2) makes p^2*a_3(n,n-i) divisible by p, and every x_i has
valuation at least four.

If q is even, c_(n,p)>0 is equivalent to 3r>=2p. The excluded factors
3n-j, 0<=j<=12, ensure in fact 3r-2p>12. For s=r-i, i<=2, this implies
p<=r/2+s. The small leading coefficient is

\[
 c_{a,5}=(-1)^{s+a}\binom ra^5
                   \binom{a+s}s\binom{r-a+s}s.
\]

It is divisible by p for every a: either a+s>=p or r-a+s>=p,
because these two inequalities cover all 0<=a<=r when p<=r/2+s.
The factorial denominators here are units modulo p. Thus A_5(r,s)
is zero modulo p, and (2) again gives valuation at least four for x_i.
These cases prove every factor in (1).

## A uniform exponential lower bound for g_n

The prime number theorem applied to (1) yields

\[
 \boxed{\liminf_{n\to\infty,\ n\text{ even}}\frac{\log g_n}{n}
 \ge c_g:=3+\frac{\pi}{4\sqrt3}+\frac34\log3
       >4.277409057559.}
 \tag{4}
\]

To detail the constant, write n=2k. The condition c_(n,p)>0 means
the fractional part of k/p is at least 1/3. Combining the eligible
primes below n with the interval (n,3n/2] gives, up to negligible terms,
the disjoint intervals

\[
 \frac{k}{j+1}<p\le\frac{k}{j+1/3},\qquad j=0,1,2,\ldots.
\]

For any fixed number of these intervals, the prime number theorem
gives half the sum of their endpoint-length differences per n.
The tail is bounded by the Chebyshev sum over p<=k/J, hence is O(n/J).
The small-prime cutoff costs o(n). Primes excluded by B_n cost O(log n),
since B_n is a fixed-degree polynomial in n. Finally

\[
 \sum_{j=0}^\infty\left(\frac1{j+1/3}-\frac1{j+1}\right)
 =3\int_0^1\frac{1+x}{1+x+x^2}\,dx
 =\frac32\log3+\frac{\pi}{2\sqrt3}.
\]

The baseline d_n^3 contributes three, proving (4).

## An unconditional upper bound for the primitive lower row

The harmonic-binomial formula gives

\[
 |a_3(n,m)|\le(n+1)216^n
             \frac{49H_{2n}^2+24}{2},\qquad 0<=m<=n.
 \tag{5}
\]

Indeed the logarithmic-jet quantities obey abs(U)<=7H_(2n) and
0<=V<=24. Each leading magnitude is at most its value at m=n.
The symmetric product binom(n+j,n)*binom(2n-j,n) is maximal at j=n/2,
as its successive ratio shows. For n=2k, the binomial theorem gives
binom(3k,k)<=(27/4)^k. Together with binom(n,j)<=2^n, this bounds each
leading magnitude by 216^n, proving (5).

For the primitive normal vector x/g_n, (4)-(5) prove

\[
 \limsup\frac{\log\|x/g_n\|_2}{n}
 \le5+3\log6-c_g<6.097869350125.
\]

This is an actual uniform arithmetic estimate. It bounds the covolume
of the cancellation lattice; it does not bound all its successive minima.
For a Gauss-reduced basis with length ratio kappa_n>=1, the geometric
inequality Q_n<=4*sqrt(kappa_n*norm(x/g_n)) follows from its angle being
at least pi/3. Controlling kappa_n and the selected positive coordinates
J_n is still required.

## The image-content candidate fails

The stronger candidate v_p(Gamma_n)>=2+c_(n,p), under the same exclusions,
is false. At n=480, p=47, all the eligibility conditions hold and

\[
 c_{480,47}=0,\qquad v_{47}(g_{480})=4,\qquad
 \boxed{v_{47}(\Gamma_{480})=1<2.}
\]

The small quotient is q=10, and 47 divides the numerator of a_3(10,10).
Thus local vanishing in the smaller coefficient can add a factor to the
lower-row gcd without supplying the asserted additional image-content
factor. The exact falsification record includes the actual gcds.

A possible aggregate repair would bound the weighted sum of these
valuation deficits by o(n), rather than asserting the false pointwise
bound. That loss estimate has not been proved. The reference density
constant 3/2+(3/2)log3 for Gamma_n is therefore not an established
estimate for this construction.

The constant computations in `prime-density-budget.json` show that this
reference content rate, together with subexponential J_n and kappa_n,
would give cost rate below 4.901017 and a positive decay margin. Those
additional assertions remain unproved. The concluding irrationality
argument cannot be applied unconditionally.

The checker records 1,188 congruence instances, checking all three
coordinates, nine explicit divisors, and 486 above-n all-block cases.
Those are implementation checks; the product, trace and carry arguments
above prove (1)-(5). They are not a completed Lean formalization or a
proof of the required image-content estimate.
