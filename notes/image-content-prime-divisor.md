# A surviving image-content divisor and a joint primitive-cost saving

Fix s=2r+1>=5, even n>=2r, and the actual blocks m=n-j, 0<=j<=r.
The kernel and its Laurent coefficients are those of the manuscript.
All asymptotic statements here are at fixed s along even n.

Put

    B_(r,n)=product_(j=0..r)(n-j) product_(j=0..2r+2)(3n-j).

Call a prime p eligible when p<=n, p>s, p^2>3n+2r+3, and p does
not divide B_(r,n). Let P_n be their product, and let A_n be the
product over the eligible primes satisfying

    c_(n,p)=floor(3n/(2p))-3floor(n/(2p))>0.

The following two divisibilities concern different objects:

    A_n divides Gamma_(s,n),                                    (1)
    P_n^(r-1) A_n divides J_n.                                 (2)

Here J_n is the gcd of the r-minors of (Cbar;Y) and (Cbar;Z).
The lower row Cbar_k is d_n^(s-k) a_k/G_(s,k,n), using the already
proved prime products above n. These rows are integers and have the
same saturated integer kernel as the original lower-period rows.
Y=d_n^s a_s and Z=d_n^s b. If delta_n is the gcd of the (r-1)-minors
of Cbar, Smith reduction gives J_n=delta_n Gamma_(s,n).

## General first-order coefficient congruence

For an eligible p write n=pq+a. The boundary exclusion gives a>r,
so m=pq+b with b=a-j for every selected block. Define

    L_s(a,b)=sum_(v=0..a) (-1)^(b+v) binom(a,v)^s
                         binom(v+b,b)binom(a-v+b,b).

This is the top Laurent-coefficient sum of the residual kernel.
The following are congruences of p-integral rational numbers:

    p^(s-k) a_k(n,m) = L_s(a,b) a_k(q,q) mod p,   k odd, 3<=k<=s,
    p^s b(n,m) = L_s(a,b) b_raw(q,q) mod p.                    (3)

The small raw kernel at q uses no extra factor 2t+q, even when q is
odd. Its rational boundary coefficient b_raw is defined by all its
Laurent coefficients, including the even orders.

To prove (3), split the poles into residue classes v modulo p and
reduce p^s T_(s,n,m)(pX-v). For v<=a, the denominator factors
divisible by p give product_(h=0..q)(X+h)^s. In the absence of a
numerator carry the divisible numerator factors give
product_(h=1..q)(X-h)(X+q+h). The factorial unit identity

    (pq+a)!/p^q = (-1)^q q! a! mod p

and its analogous expressions for m give exactly

    p^s T_(s,n,m)(pX-v)
      = l_(s,v)(a,b) T_(s,q,q)(X) mod p,

where l_(s,v) is the v-th summand defining L_s. A numerator carry
makes both sides zero modulo p. For v>a the denominator has only q
complete p-factors and the left side is zero modulo p. The assumption
p^2>3n+2r+3 ensures that all factorial arguments are below p^2.
Summing the residue classes proves the rational-function congruence
with factor L_s(a,b).

For the coefficient sums, a pole j becomes the pole floor(j/p) only
in its own residue class. Its order-k coefficient is multiplied by
p^(s-k). All other translated principal parts reduce to zero: their
denominators are units and their coefficients after multiplication by
p^s are divisible by p^k. These valuation bounds follow from the
weighted Taylor denominator theorem. The small integer poles remain
distinct modulo p because q<p. This proves the first line of (3).

For the rational boundary use the exact decomposition

    H_(j,k)=p^(-k) H_(floor(j/p),k)+U_(j,k), U_(j,k) in Z_(p).

The contribution p^s c_(j,k) U_(j,k) has valuation at least k>=1
and disappears modulo p. The remaining terms are exactly the rational
boundary of the small raw kernel. This proves the second line.

## Which primes make the residual factor vanish

If q is odd, a is odd since n is even and p is odd. Reflection
v->a-v changes the sign of l_(s,v) because s is odd, and therefore
L_s(a,b)=0 as an integer.

If q is even, c_(n,p)>0 means 3a>=2p. The excluded factors 3n-j
ensure 3a-2p>2r+2, hence a+2b=3a-2j>=2p for every j<=r.
For every v either v+b>=p or a-v+b>=p. Its corresponding binomial
factor is divisible by p, while both factorial denominators are units.
Thus L_s(a,b)=0 modulo p in this case too. In both cases, (3) makes
all the scaled coefficients zero modulo p, including p^s b(n,m).

Since v_p(d_n)=1, every entry of the cleared rational row Z is then
divisible by p. Every entry of Y=d_n^s a_s is divisible by p as well,
because a_s is an integer. Therefore p divides both coefficient images
of every integer cancellation vector, proving (1). No division by the
lower-row gcd occurs in this inference. The Lean lemma
entries_dvd_image_content formalizes the implication for arbitrary
integer rows and any finite family of integer vectors.

## Joint minors avoid the lower-content loss

For every eligible prime, the naturally scaled lower-period rows
and rational row in (3) form a matrix of rank at most one modulo p:
the scalar L_s(a,a-j) depends on the column j, while the small-kernel
coordinates depend on the row. Multiplying each row by a p-adic unit
preserves this property. Dividing the lower rows by their products
G_(s,k,n) above n also only multiplies by units at p<=n. The cleared
target row Y is zero modulo p. Thus both augmented matrices
(Cbar;Y) and (Cbar;Z) have rank at most one modulo p.

An r-by-r matrix with rank at most one modulo p has determinant
divisible by p^(r-1). To see this, lift an invertible row reduction
over F_p; if a nonzero pivot exists it leaves r-1 rows divisible by p,
and if no pivot exists all rows are divisible by p. The lift has unit
determinant in Z_(p), so the valuation conclusion is unchanged.

At primes dividing A_n all entries of both augmented matrices vanish
modulo p, and their r-minors are divisible by p^r. Multiplying over
distinct eligible primes proves (2).

Let w_1,w_2 be the usual two Cramer kernel vectors of Cbar. Every
coordinate is an (r-1)-minor, so delta_n divides each coordinate.
Then v_i=w_i/delta_n is an integer kernel vector and Gamma divides
both its coefficient images. Their relative masses satisfy exactly

    norm_1(v_i)/Gamma=norm_1(w_i)/J_n.                          (4)

The vectors remain independent, and full augmented rank makes their
coefficient images independent. Thus these are legitimate integer forms,
and dividing each by its own content can only decrease its cost. No
positivity assumption is needed. This is a joint saving
in the kernel coordinates and image content, not a second independent
lower bound on Gamma from the rank-one congruence.

## Asymptotic rates and the actual resulting cost bound

The excluded small primes contribute O(sqrt(n)) to log P_n, and primes
dividing B_(r,n) contribute O(log n). The prime number theorem gives

    log(P_n)/n -> 1.

The condition c_(n,p)>0 is equivalent to frac(n/(2p))>=1/3.
The prime intervals n/(2(l+1))<p<=n/(2(l+1/3)) have disjoint
interiors. Their full endpoint-length sum is

    (1/2) sum_(l>=0)(1/(l+1/3)-1/(l+1))
      =pi/(4sqrt(3))+(3/4)log3.

Restriction to p<=n removes the interval n<p<=3n/2, of rate 1/2.
The tail after l=L is bounded by theta(n/(2L))=O(n/L). Applying
the prime number theorem to finitely many intervals, then letting L
increase, proves the ordinary limit

    log(A_n)/n -> c0=pi/(4sqrt(3))+(3/4)log3-1/2
                     =0.777409057559... .

In particular, the new unconditional conclusion is

    liminf log(Gamma_(s,n))/n >= c0.                           (5)

For a concrete relative-cost upper bound, let E_s(n) be the established
central-binomial envelope of rate b_s=(s-2)log2+3log3. Cramer's mass
bound, (2), and (4) give an independent pair of integer forms with
relative cost at most

    r! d_n^(r(r-1)) E_s(n)^(r-1)
       /[ product_(k odd,3<=k<=s-2) G_(s,k,n) P_n^(r-1) A_n ]. (6)

The upper logarithmic rate of (6) is

    r(r-1)+(r-1)b_s-((s-2)/2) H_(r-1)-c0.                    (7)

At weight seven this is approximately 14.995737, whereas the proved
sharp analytic budget a_7-7 is approximately 0.781973. Thus (1)-(7)
are additional arithmetic estimates for the actual family, but they
still do not prove the desired negative full rate. The rank-one saving
is counted in J_n, not counted again in Gamma after lower-row division.
The all-odd irrationality theorem remains unproved.

The exact script checks eight actual profiles, 315 first-order
congruences, the image divisor, the joint-minor divisor, and (4).
The local factorial congruence, prime asymptotic, and Cramer-family
identification above are paper proofs. The three new Lean lemmas verify
entry divisibility under integer pairings and image contents; they do
not constitute a full formalization of (3) or (5).
