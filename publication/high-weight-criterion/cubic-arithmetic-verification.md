# Exact cubic arithmetic and the Guth-Maynard proposal

The desired all-index growth bound below log(2397)-7 has not been proved.
This continuation gives an explicit integer formula for that target,
proves its local content properties, and checks which modern analytic
inputs can actually be applied.

## Exact target and proved arithmetic

Let M_n be the full cleared coefficient matrix, delta=det(M_n),
v_i the constructed normalized vector, and x_i=delta*v_i in Z^4.
Put F=n^2(n-1)^2(n-2)^2. The manuscript writes an explicit integer
matrix R_n such that the cubic coefficients are

  q_(ell,n,i)=b_(ell,n,i)/(F*delta), b_i=R_n*x_i.

For g_b=gcd(b_i) and the weighted primitive integer-polynomial height
H_prim=sum abs(b_ell/g_b)*(12n^2)^ell, the exact equation is

  J_(n,i)=g_b*H_prim/(F*abs(delta)).

The proof does not drop numerator content or denominators. In particular,
a claim involving only a larger gcd is not substituted for this ratio.
The all-index identities establish

  g_x divides g_b, and (g_b/g_x) divides F,
  norm(v_i)_1 <= J_(n,i) <= 43904*norm(v_i)_1,
  lambda_2(L_n) <= max_i J_(n,i) <= 87808*lambda_2(L_n).

Thus the local content change is supported on primes dividing
n(n-1)(n-2), and its total logarithmic size is O(log n). The cubic
height and optimal primitive cost have exactly the same upper
exponential rate. The existing elementary prime-product argument gives
a completely explicit all-index upper envelope for J_n, but its exponent
is 17/4+10log(2)+6log(3), about 17.7732. That upper envelope does not meet
the required threshold. It is not a lower bound on the actual height.

## Modern inputs checked

[Guth-Maynard, New large value estimates for Dirichlet polynomials,
version 2](https://arxiv.org/html/2405.20552v2), Theorem 1.1,
controls how many separated parameters give large values of a bounded-
coefficient Dirichlet polynomial. Corollary 1.3 gives prime counts for
interval lengths between x^(17/30+epsilon) and x^0.99. These theorems
do not specify the local valuation of our hypergeometric Cramer minors.
No representation linking our exceptional valuations to their separated
large-value set has been established.

[Chen-Gupta-Li, Large Value Estimates for Dirichlet Polynomials with
Characters and Zero Density of Dirichlet L-Functions, version 2](https://arxiv.org/html/2507.08296v2)
extends the method to character twists. Its Theorem 1.1 requires a bounded
coefficient sequence, separated character/height pairs, a large-value
threshold, and a relation between polynomial length and modulus/height.
The GCDs inside its affine-correlation estimates are not identified with
the coefficient contents in our exact formula. No such identification is
assumed here.

There is a precise limit to a boundary-only application: for a fixed
number of windows of width O(n^theta), theta<1, primes of size O(n),
and bounded valuation weights, even the trivial integer count bounds
the total contribution by O(n^theta log n)=o(n). Such windows cannot
supply a new constant multiple of n in the saving. This does not rule
out a different construction or a proved valuation rule on a set of
positive total log-prime weight.

The remaining arithmetic task is therefore to control the actual
height-to-determinant ratio in the displayed equation, or to prove a
local valuation formula together with the archimedean primitive height
bound that implies it. The modern prime-distribution theorems do not
by themselves complete that task.

## Lean and independent checks

`CubicArithmeticFrame.lean` proves five statements: three inverse
Newton-frame identities, common-divisibility equivalence for every
integer modulus, and its coprime-scale specialization. The modulus is
arbitrary, so this includes every prime power. The module and
`VerifyCubicArithmetic.lean` compiled successfully. The five dependency
records in `cubic-arithmetic-axioms.log` use only propext and Quot.sound;
no new mathematical axioms or placeholders are used.

The actual factorial-kernel identification, gcd comparison, weighted
norm equivalence, and exponential-rate comparison are paper proofs.
`scripts/check_cubic_arithmetic_frame.py` independently checks the
integer matrix, its determinant, exact rational profiles, gcd quotient,
primitive height ratio, and both norm inequalities on the ten stored
forms at n=6,8,12,20,40. The records are in
`notes/cubic-arithmetic-frame.json`. No new asymptotic assertion is
inferred from those checks.

The existing manuscript was edited in place and checked using its
built-in compiler. No separate PDF was compiled.
