# An exact integer hypergeometric transformation of the existing kernel

This pass derives a Pfaff--Saalschutz identity for the actual rational
kernel, a positive multiple-integral presentation, and an explicit
all-index bound for the transformation coefficients. These results do
not yet prove the required primitive cost rate or all-odd irrationality.
The manuscript is unchanged in this pass.

Write (x)_k=x(x+1)...(x+k-1). For n>=1, 0<=m<=n and odd s>=3, retain

    T_(s,n,m)(t)=(n!)^s/(m!)^2
       * (t-m)_m (t+n+1)_m / (t)_(n+1)^s.

## Exact terminating identity and integer coefficients

Define

    c_j=(-1)^j binom(n+2m+1,m-j) binom(n+j,j),  0<=j<=m.

Then, as an identity of rational functions,

    T_(s,n,m)(t)=sum_(j=0..m) c_j R_j(t),
    R_j(t)=(n!)^s/(2m)! * (t-m-j)_(2m)/(t)_(n+1)^s.

Every c_j is an integer. Each R_j has zeros at all positive integers
1,...,m+j, so its sum can be started at 1 without a boundary correction.
Its numerator also cancels one order at the denominator poles
0,-1,...,-(m-j-1), when j<m. Thus the canceled poles are explicit.
Individual R_j need not have only odd periods; the integer combination
restores exactly the original kernel and its parity.

Proof: divide the claimed polynomial numerator identity by
c_0*(t-m)_(2m) at generic t. Its left sum becomes

    3F2(-m,n+1,m+1-t; n+m+2,1-t-m; 1).

The second lower parameter is precisely the balanced one in the
[Pfaff--Saalschutz summation, DLMF 16.4.3](https://dlmf.nist.gov/16.4.E3).
The sum therefore equals

    (m+1)_m (n+t+1)_m / [(n+m+2)_m (t)_m].

Since c_0=(n+m+2)_m/m! and (m+1)_m=(2m)!/m!, multiplication proves

    sum_j c_j (t-m-j)_(2m)
      = binom(2m,m) (t-m)_m (t+n+1)_m.

This equality extends to all t as a polynomial identity, including
the exceptional t excluded by intermediate divisions.

## Quantified size of the integer transformation

Let W_(n,m)=sum_j |c_j|. Its positive-coefficient generating formula is

    W_(n,m)=[z^m](1+z)^(n+2m+1)/(1-z)^(n+1).

For m=n-r and z0=2-sqrt(3), coefficient positivity gives

    W_(n,n-r) <= (sqrt(3)/6^r) (6sqrt(3))^n.

Indeed substitute z0 into the generating function and divide by z0^m.
The exponential factor is
(1+z0)^3/[(1-z0)z0]=6sqrt(3), and the remaining factor is
z0^r(1+z0)^(1-2r)/(1-z0)=sqrt(3)/6^r.
This proves a fixed-r upper exponential rate log(6sqrt(3)) for these
specific transformation multipliers. It is not a rate for Gamma or
the primitive coefficient profiles. The squared bound is purely integral:

    W_(n,m)^2 6^(2(n-m)) <= 3*108^n.

The coefficient gcd divides binom(2m,m), since their signed sum equals
that binomial coefficient by comparison of leading terms in the
polynomial identity. Any content saving must be tracked against the
explicit denominator (2m)! in R_j; it is not automatically a saving
for the final primitive form.

## The actual series and the proposed Whipple/Bailey formulas

Put b=m+1, a=n+2m+2, B=n+m+2. Direct term ratios give

    A_(s,n,m)=T_(s,n,m)(m+1)
       * (s+2)F_(s+1)(a,b,...,b; B,...,B; 1),

with s+1 copies of b and B. It is well-poised because b+B=a+1.
The standard very-well-poised Whipple/Bailey specialization requires
the special upper/lower pair 1+a/2,a/2. That pair is not present:
B-a/2=n/2+1>0. Thus the standard 7F6 or 9F8 formula cannot simply be
inserted with these parameters. The terminating identity above is an
applicable transformation, with every coefficient explicitly accounted for.

## A positive higher-dimensional integral and an Euler reduction

Beta integration and the binomial series give the exact identity

    A_(s,n,m)=(n+2m+1)!/[n!(m!)^2]
      * integral_([0,1]^(s+1))
        product_i x_i^m(1-x_i)^n /(1-product_i x_i)^(n+2m+2) dx.

All terms are positive. Tonelli's theorem justifies expansion; the
series convergence excess s(n+1)-2m-1 is positive. The prefactor follows
by canceling the beta normalizations against T(m+1).

For P in [0,1), the one-variable integral in this construction is

    integral_0^1 x^m(1-x)^n/(1-Px)^(n+2m+2) dx
      = Beta(m+1,n+1) (1-P)^(-2m-1) Q_m(P),
    Q_m(P)=2F1(-m,n+1;n+m+2;P).

This is the [Euler transformation, DLMF 15.8.1](https://dlmf.nist.gov/15.8.E1).
It can also be proved directly by x=(1-u)/(1-Pu). After substitution
the integrand becomes

    (1-P)^(-2m-1) u^n(1-u)^m(1-Pu)^m.

Expanding the last polynomial shows
binom(n+2m+1,m)*Q_m(P)=sum_j c_j P^j. Consequently

    A_(s,n,m)=integral_([0,1]^s)
       product_i x_i^m(1-x_i)^n
       * [sum_j c_j P^j]/(1-P)^(2m+1) dx,
    P=product_i x_i.

The terminating polynomial is positive on [0,1), despite its alternating
coefficients, by its displayed positive beta-integral representation.
These expressions provide extra integration variables and explicit
arithmetic factors without assuming a new motivic or Galois realization.
They do not evaluate a primitive gcd or bound the reduced moment minimum.
No unproved geometric identification is used to replace that task.

## Verification and outcome

`saalschutz_kernel_transform.py` checks 120 complete polynomial identities
for 0<=m<=n<=14, including the integral squared norm bound. It separately
checks 360 rational one-dimensional integrals by exact antiderivatives,
48 hypergeometric terms, and rational kernel evaluations at six sample
parameter triples in weights 5,7,9,11. All pass. The all-index identities
follow from the summation and beta proofs, not these finite tests.

This is a concrete transformation of the unchanged kernel with proved
integer multipliers and a controlled multiplier rate. It does not yet
give the final negative primitive-cost rate. The complete transformed
period coefficients and cancellation weights would have to be bounded
together before claiming such a rate. These new family identities are
paper proofs and have not been formalized in Lean in this pass.
