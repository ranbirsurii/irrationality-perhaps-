# A three-block enlargement using the uniform arithmetic already proved

The two-block spectral shortcut is not used here. This construction
enlarges the family to lengths n,n-1,n-2, applies the established uniform
coefficient denominator and positive-sum bounds, and selects positive
integer cancellation weights in an exactly computed lattice.

It defines nonzero primitive forms at every even n>=2. Exact finite
certificates through n=1280 give forms strictly between zero and one;
the last is below 10^(-126). A uniform limiting bound for the new weight
selection has not been proved. No irrationality theorem or completed
Lean formalization is claimed, and no further compilation was performed.

## Why adding a block can change the outcome

In the two-dimensional rational span of two independent coefficient
vectors, imposing one nonzero lower-period linear constraint leaves a
one-dimensional line. Any invertible rational row change preserves that
line. Its primitive integer coefficient pair is therefore unchanged up
to sign. Such a change can alter a triangle-inequality upper bound, but
does not improve the actual primitive error.

Adding the third block allows genuinely different cancelled forms. The
three-column coefficient matrices have nonzero determinants at every
audited index. No all-index rank-three theorem for this new profile is
needed for the construction or asserted on the basis of those checks.

## Uniform denominator and positivity statements apply

For even n>=2 use the normalized kernels T_(n,m) already defined, with
m=n,n-1,n-2. The proved paper denominator theorem applies because
0<=m<=n. Thus D=d_n^5 clears each rational coordinate triple:

\[
 D\mathcal A_{n,n-i}=x_i\zeta(3)+y_i\zeta(5)+z_i,
 \qquad (x_i,y_i,z_i)\in\mathbb Z^3,\quad i=0,1,2.
\]

This is precisely the uniform arithmetic used, with no new denominator
estimate assumed. The existing global adjacent-sign theorem gives
x_0*x_1<0. Each sum is strictly positive, and all three have logarithmic
rate lambda_5 because their block offsets are fixed.

Consequently positive integer vectors w with x*w=0 exist at every even
index: one can always use the two-block vector supported on entries 0,1.
For every such vector,

\[
 A=\sum_iw_i y_i,\quad B=\sum_iw_i z_i,\quad
 h=\gcd(|A|,|B|)>0,\quad M=\sum_iw_i,
\]

and

\[
 0<L_n=\frac{A\zeta(5)+B}{h}
   =\frac D h\sum_iw_i\mathcal A_{n,n-i}
   \le\frac{DM}{h}\max_i\mathcal A_{n,n-i}.
 \tag{1}
\]

The strict positivity proves the pair (A,B) is nonzero; it also proves
nonvanishing after primitive normalization without assuming irrationality.
The coefficient of zeta(5) need not separately be assumed nonzero.

## An exact saturated cancellation lattice

Let g_01=gcd(x_0,x_1), choose u*x_0+v*x_1=g_01, and put
g=gcd(x_0,x_1,x_2). The vectors

\[
 b_0=(x_1/g_{01},-x_0/g_{01},0),\qquad
 b_1=(u x_2/g,v x_2/g,-g_{01}/g)
\]

form a basis of the full integer kernel of the row x. Indeed, for any
integer solution w the third coordinate is a multiple of g_01/g, since
g_01 divides x_2*w_2 and gcd(g_01/g,x_2/g)=1. Subtracting a multiple of
b_1 eliminates that coordinate. The remaining two-coordinate relation
is an integer multiple of b_0. This proves saturation, not just rational
spanning.

Integer Gauss reduction changes this basis by unimodular operations.
The implementation additionally checks that its cross product is
plus or minus x/g, an exact certificate of the lattice covolume.
It enumerates primitive pairs (s,t) with abs(s),abs(t)<=20, retaining
one-sign vectors s*b_0+t*b_1, and includes every available nonnegative
two-block ray. It removes any common weight factor and chooses the
candidate minimizing K=DM/h by exact rational comparisons.

The fallback two-block ray exists at every even index. The selection is
therefore a finite, total definition of an all-index positive sequence.
The search is not asserted to find a global optimum outside its finite
box and listed rays.

## A uniform arithmetic bound adapted to the enlarged lattice

For either reduced basis vector b_j, form the integer image

\[
 v_j=(b_j\cdot y,b_j\cdot z),\qquad
 \Gamma_n=\gcd\{(v_j)_k:j=0,1,\ k=0,1\}>0.
\]

Every integer lower-period cancellation lies in this kernel basis.
Hence Gamma_n divides both output coordinates and h>=Gamma_n. This
content is basis independent. Equivalently,

\[
 g\Gamma_n=
 \gcd_{0\le i<j\le2}
   (x_i y_j-x_j y_i,\ x_i z_j-x_j z_i).
\]

For a proof, use integer row operations sending the distinguished
column x to (g,0,0). The other two rows are the kernel images in a
unimodularly equivalent basis. The selected minors are then g times
their four coordinates, together with zeros. Their gcd is unchanged
by the induced unimodular compound transformation.

Write the selected vector uniquely as w=s*b_0+t*b_1 and set

\[
 J_n=\max(|s|,|t|),\qquad Q_n=\|b_0\|_1+\|b_1\|_1.
\]

Since M<=J_n Q_n, the following bound holds at every index:

\[
 \boxed{K_n\le\frac{d_n^5 J_n Q_n}{\Gamma_n}.}
 \tag{2}
\]

This adapts the uniform arithmetic to the new situation and accounts
for the selected weights explicitly. It is not yet a negative exponential
bound. For that, it would suffice to prove

\[
 \limsup\frac{\log J_n+\log Q_n-\log\Gamma_n}{n}
                       <-5-\lambda_5.
 \tag{3}
\]

An estimate of this kind along an unbounded subsequence would also
suffice; an all-index limit is stronger than the irrationality argument
requires. Neither form of (3) has been proved here. The uniform
denominator theorem alone does not control these three lattice terms.

## Exact finite sum bounds, without numerical zeta evaluation

The positive summand has ratio

\[
 \frac{T_{n,m}(k+1)}{T_{n,m}(k)}
 =\frac{k^6(k+n+m+1)}{(k-m)(k+n+1)^6}.
\]

The established unimodality proof locates the first index k_* where
this ratio is at most one; it is a maximum summand. The existing
uniform tail bound gives, with

\[
 E=5(n+1)-2m-2,\quad B=2m^2+5n(n+1),\quad
 C=\max\{2m,m+1,\lceil B/E\rceil\},
\]

the exact enclosure

\[
 T_{n,m}(k_*)\le\mathcal A_{n,m}
                    \le(2C+1)T_{n,m}(k_*).
\]

The maximum is computed entirely rationally from

\[
 T_{n,m}(k)=
 \frac{(n!)^5((k-1)!)^6(k+n+m)!}
 {(m!)^2(k-m-1)!((k+n)!)^6}.
\]

Multiplying the three intervals by D*w_i/h and summing yields rigorous
positive lower and upper bounds on the actual primitive form (1).
Thus the reported smallness is an analytic certificate, not an estimate
based solely on coefficient sizes or decimal values of zeta.

## Finite results and the remaining conclusion

The exact records in `three-block-lattice-audit.json` contain the full
coordinate matrices, saturated reduced bases, positive integer weights,
primitive coefficient pairs, removed gcds, and rational interval bounds.
The following rates are rounded summaries of rational enclosures:

| n | log(K_n)/n | log(upper bound in (2))/n | log(primitive-form upper bound)/n |
|---:|---:|---:|---:|
| 20 | 4.695074 | 5.278006 | -0.413091 |
| 40 | 4.533861 | 4.815617 | -0.561003 |
| 80 | 4.714671 | 4.917019 | -0.340470 |
| 160 | 4.680572 | 4.822657 | -0.349699 |
| 320 | 4.800570 | 4.834829 | -0.203964 |
| 640 | 4.764118 | 4.794027 | -0.225482 |
| 1280 | 4.754680 | 4.777352 | -0.227174 |

At every audited n=2,4,8,12,20,40,80,160,320,640,1280, the actual form
is certified strictly between zero and one. The mass-normalized maximum
upper bound in (1) is also below one at every listed n>=4. At n=1280,
an exact integer comparison certifies

\[
 \boxed{0<L_{1280}<10^{-126}.}
\]

If zeta(5)=p/q with positive integer q, then q*L_1280 is a nonzero
integer. This finite certificate consequently forces q>10^126. It does
not exclude every possible denominator and therefore is not an
irrationality proof.

The improved form changes the cancellation direction and keeps
denominator cost and nonvanishing explicit. The remaining task is proving
(3), or a sufficient subsequence version, rather than treating its
finite values as an established limit. The computations are not being
presented as a final Lean theorem or an arXiv-ready irrationality paper.
