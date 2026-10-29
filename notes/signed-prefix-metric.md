# Exact signed-prefix cancellation and its large-index rate identity

This is a sharper majorant for the actual family, not a proof that its
primitive cost tends to zero. All index statements in the derivation
are valid for fixed odd s=2r+1>=7 and eligible even n.

## 1. Preserve the prefix before squaring

Put m=n-r, T=T_(s,n,m), w(k)=k(k+n)/(12n^2), and K>=3n.
Let P_z(w)=sum_(i=0..r) z_i w^i. Define rational prefix moments

    m_j=sum_(m<k<=K) T(k) w(k)^j,  P=m_0>0.

Write a=sum_i z_i m_i and b=sum_(k>K) T(k)P_z(w(k)).
Let tau_j majorize the corresponding infinite tail moments, and put

    E_z=(r+1)sum_i z_i^2 tau_(2i),  mu=P+tau_0.

The pointwise inequality P_z(w)^2<=(r+1)sum_i z_i^2 w^(2i)
and weighted Cauchy-Schwarz give b^2<=tau_0 E_z. Consequently

    (a+b)^2 <= mu*(a^2/P+E_z).                         (1)

There is no absolute value inside the finite sum defining a. For any
real z the finite variance identity proves

    a^2/P <= sum_(m<k<=K) T(k) P_z(w(k))^2.            (2)

Thus the new metric is no larger than the old moment metric as a
quadratic form, for every profile, not just tested vectors.
Its matrix is

    G_prefix=(m_i m_j/P)_(i,j)+(r+1)diag(tau_0,tau_2,...,tau_(2r)).

## 2. A tail power growing with n

Logarithmic differentiation, using t>=2m, gives

    (log T)'(t) <= -E/t+B/t^2,
    E=s(n+1)-2m,  B=2m^2+s*n(n+1).

For example 1/(t-h)<=1/t+2h/t^2,
1/(t+n+h)<=1/t, and 1/(t+j)>=1/t-j/t^2 prove this
with the smaller coefficient m(m+1)+s*n(n+1)/2, which is <=B.
One may choose p=E-ceil(B/K), requiring p>4r+1. Then

    T(t)<=T(K)*(K/t)^p  for t>=K.

Integral comparison of the decreasing power function proves the explicit
tail certificate

    tau_j=T(K)*K/(p-2j-1)*(K(K+n)/(12n^2))^j, 0<=j<=2r. (3)

This accounts for the entire infinite tail; it is not a numerical cutoff.
The implemented sharper choice works for every K>m:

    p=floor(s*sum_(j=0..n) K/(K+j)-m-sum_(h=1..m) K/(K-h)).

Indeed t/(t-h) decreases and t/(t+j) increases for t>=K, whereas
t/(t+n+h)<=1. Substitution in t*T'/T proves it is <=-p.
Formula (3) is unchanged. For this sharper choice and K=cn,

    p/n -> s*c*log((c+1)/c)-1-c*log(c/(c-1)).

At c=5/4 this limit is >1 for every s>=7. For example log(9/5)>4/7
and log(5)<=9/4 give a lower bound >19/16 at s=7, increasing with s.
Lean checks this positivity. Thus p>4r+1 eventually at every fixed weight.
The following coarse-choice calculation is an additional alternative.
For fixed integer c>=3 and K=cn, as n tends to infinity,

    p/n -> d_s(c)=s-2-(s+2)/c>0,
    tau_j/T(cn) -> c/d_s(c)*(c(c+1)/12)^j>0.          (4)

The first limit follows from ceil(B/K)-B/K in [0,1). The second follows
by dividing p-2j-1 by n in (3). In particular their logarithmic rates
are exactly equal, not merely bounded in the same direction.
Stirling's factorial formula in the exact kernel gives

    log tau_j/n -> Phi_s(c),
    Phi_s(x)=(s+1)x log x+(x+2)log(x+2)
             -(x-1)log(x-1)-(s+1)(x+1)log(x+1).

The O(1) offsets m=n-r and the factorial endpoints contribute O(log n)
to the logarithm. This proves a genuine all-index tail rate. It does
not assert a rate for an integer minimum after the coefficient pullback.

## 3. Exact large-index equality for the complete cost

Let F carry an integer coefficient pair y to its rational profile, as in
the existing moment construction. Put Q=D^2 F^T G_prefix F,
where D=d_n^s. The exact form identity and (1) give

    |y_1*zeta(s)+y_2|^2 <= mu*y^T Q y.

Reduce Q over GL_2(Z) to [[alpha,beta],[beta,nu]], with
0<alpha<=nu and 2|beta|<=alpha. Its determinant Delta is positive.
For R=mu*nu and C=mu*Delta/alpha one has

    C<=R<=(4/3)C,
    0<=(log R-log C)/n<=log(4/3)/n.                 (5)

Hence the normalized logarithmic difference tends to zero without
assuming either rate has an ordinary limit. Their upper logarithmic
rates coincide. This equality holds for all eligible large indices;
it does not determine the sign of that common rate.

The determinant also has an exact rank-one formula. Write H for the
pulled-back tail metric, q for the pulled-back prefix moment row, and
Q=H+q*q^T/P. Then

    det Q=det H+(q_1^2 H_22-2q_1q_2 H_12+q_2^2 H_11)/P.

This identity is checked exactly in the script, including all D factors.

## 4. Attempt to turn the improvement into an explicit basis bound

Write the rational prefix row as q=(a/t,b/t), gcd(a,b)=1, t>0 rational.
Choose integers x,y with ax+by=1 and x^2+y^2<=a^2+b^2=N.
Such a choice follows by centering a Bezout solution modulo (b,-a):
its squared norm is 1/N plus a centered determinant squared divided by
N; for N>=2 this is at most 1/N+N/4<=N. The case N=1 is immediate.
The two vectors (b,-a),(x,y) form a unimodular basis. Since a positive
semidefinite tail matrix H satisfies v^T H v<=tr(H)||v||^2, this proves
the unconditional upper bound

    R <= mu*(1/(t^2 P)+tr(H)*N).                    (6)

All quantities on the right are exact rational functions of the prefix
and tail certificates. This is a constructive basis estimate, not a
claim that an area controls the second minimum. It was tested at every
recorded index. Unfortunately, its right side is large: at weight seven,
n=160, K=960, its logarithm exceeds 15307. The reduced metric itself
has log(R)<-2025. Thus this direct basis construction does not yet prove
the required uniform contraction, despite the finite improvement.

## 5. Verification and exact finite consequences

The script uses exact rational arithmetic at weights 7,9,11 and forty
index/cutoff combinations, including n=160 and K=960. It checks:

- the infinite-tail budget and positivity;
- positive semidefinite improvement of the pulled-back binary metric;
- the rank-one determinant identity and the 4/3 sandwich;
- two unimodular primitive coefficient pairs in each case;
- their complete squared bounds against independent zeta enclosures;
- separately, the actual signed-prefix residual against the tail bound;
- the constructive Bezout upper bound (6).

At weight seven, n=160, K=960 the squared bound is <10^(-878).
Thus if zeta(7)=p/q, necessarily |q|>10^439: one of two independent
integer forms is nonzero, so 1<=|q|sqrt(R). This finite denominator
exclusion is not irrationality.

Lean verifies weighted finite-prefix energy, the two-piece Cauchy bound,
the exact energy gain when merging prefixes, the derivative tail-power
budget, the logarithmic sandwich error and its limit, and the integer
denominator implication. Infinite summation, the family pullback and the
Stirling limit (4) are paper proofs here. No all-index negative rate for
R, no lower bound on alpha establishing that rate, and no unconditional
all-odd irrationality conclusion has been proved in this continuation.

## 6. Explicit integer forms, with an arithmetic Lean certificate

At weight seven, n=8, K=48, the selected pairs are

    (22177603708244749601, -22362770673271245300),
    (14836825409810353538, -14960702180624020999).

The generated WeightSevenIntegerCertificate.lean contains the four
integer coefficient rows and the two integer block vectors. It verifies
their exact lower-period cancellations, coefficient contents, coprimality,
unimodular coefficient determinant, and nonvanishing at any real input.
It also checks the exact rational metric reduction and the complete bound
D^2*mu*nu<10^(-38), retaining the denominator-clearing factor.
The coefficient matrix is independently checked in Python using both
logarithmic jets and direct truncated rational-series products.

The finite Lean certificate checks arithmetic on these displayed integer
and rational objects. It does not formalize their analytic identification
with the zeta series, nor a bound for every n. That analytic identification
uses the established paper partial-fraction identity and the tail proof.
