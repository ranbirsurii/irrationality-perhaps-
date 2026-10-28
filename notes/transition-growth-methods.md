# Exact transition norm and the proposed growth methods

This pass uses the supplied list as proposed research tools, not as
established estimates. It proves an exact operator formula and a directional
lower certificate. It does not establish the uniform rate or irrationality.

## The quantity to estimate

Fix s=2r+1 and an eligible even n in the original consecutive-block family.
Let M be its full integer coefficient matrix and let E embed a pair (a,b)
in the last two coefficient positions. Let H be the rational map taking a
block vector to its polynomial profile, with coefficient ell multiplied
by (12n^2)^ell. Set

    F = H M^(-1) E = [u v].

The actual transferred height is exactly

    J(a,b) = sum_ell |a*u_ell + b*v_ell|.

Every matrix entry here is explicit and rational. Full rank makes M
invertible, and the triangular Newton profile map makes H invertible.
Thus the two columns u,v are independent. No arithmetic normalization
is omitted in this formula.

## Exact operator estimate

Define P=sum|u+v|, Q=sum|u-v|, and T=max(P,Q). Then

    J(a,b) <= T max(|a|,|b|),
    ||F||_(infinity -> 1) = T.

Proof: the square [-1,1]^2 is the convex hull of its four vertices.
For a normalized pair, express it as their convex combination and use
convexity of the absolute-value sum. At the vertices the values are P,Q,
P,Q; one attains T. Homogeneity gives the bound for any pair, including
the zero pair. This proves optimality among all direction-independent
constants multiplying max(|a|,|b|).

If B=sum|u|+sum|v| is the elementary triangle envelope, then

    max(sum|u|,sum|v|) <= T <= B <= 2T.

Indeed 2u=(u+v)+(u-v), and similarly for 2v, so each column norm is at
most (P+Q)/2<=T. The remaining inequalities follow by the triangle
inequality. Consequently this optimal operator norm and the triangle
envelope have exactly the same exponential limsup rate: their log
difference divided by n is at most log(2)/n. Optimizing only this norm
cannot create a missing positive exponential saving.

This does not rule out exponentially better cancellation for the actual
pair (a,b). That is why estimating J(a,b) directly can be stronger than
separately estimating T and the pair size.

## Exact directional certificate

The convex piecewise linear function f(t)=sum|u_ell+t*v_ell| is coercive
since v is nonzero. Its minimum is attained at a breakpoint
t=-u_ell/v_ell with v_ell nonzero, or on an interval having such an
endpoint. Therefore

    m = min_(v_ell != 0) sum_k |u_k - (u_ell/v_ell)*v_k|
    |a| m <= J(a,b).

For a!=0, use t=b/a and homogeneity; for a=0 the lower bound is zero.
Independence of u,v gives m>0. This is a rational lower certificate,
not an upper bound. It tests whether a proposed estimate for this
particular transferred pair is compatible with its direction.

## Rate target

For fixed s>=7, the existing analytic estimate is

    |L| <= C_s (n+1)^(2s+2) d_n^s J(a_n,b_n)
                     (2397*4^(s-7))^(-n).

Writing A_s=log(2397*4^(s-7)), the sufficient arithmetic target is
limsup log J(a_n,b_n)/n < A_s-s, using log(d_n)/n -> 1.
A sufficient, potentially weaker split is

    limsup log T_n/n + limsup log max(|a_n|,|b_n|)/n < A_s-s,

when the two upper limits are finite. Neither rate inequality is proved.
Nonvanishing must also be retained; the derivative-family tests are not
an all-index nonvanishing theorem.

## Systematic assessment of the supplied tools

* Saddle point, Mellin--Barnes, and residue scaling: apply first to the
  explicit factorial coefficients and cofactors. They can bound unreduced
  entries. To estimate J they must additionally control inverse determinants
  and the primitive pair. The raw-kernel saddle already supplies A_s, not J.
* Darboux, Pringsheim, Hayman, Tauberian, Wiman--Valiron, Jensen, and
  Hadamard methods: require an independently controlled generating or
  analytic function for the relevant height or a valid majorant. Defining
  its generating series alone supplies no radius estimate. Nonnegativity
  of J does not determine the radius.
* Poincare, Perron, Birkhoff--Trjitzinsky, WKB, Frobenius, Floquet,
  Sturm comparisons, cocycles, WZ, and holonomic closure: first require
  an exact recurrence or a proved majorant for the height in question.
  Recurrences for raw coefficients do not automatically pass through
  gcd reduction, inversion, and absolute values. A derived recurrence
  also needs control of the selected solution's connection coefficients.
* Concentration, large deviations, martingales, normal approximations,
  mixing, and extreme-value methods: no probability representation or
  independence/mixing structure for this deterministic primitive height
  has been constructed here. They currently provide no applicable bound.
* Dwork, Newton polygons, Kummer--Lucas, and Iwasawa methods: potentially
  relevant to exact common divisors, but require congruences for these
  particular minors after normalization. An abstract Frobenius or valuation
  theorem does not identify those divisors. Mahler, Baker, and height
  lower bounds have no established implication giving this required
  upper bound; differential-system transcendence criteria also require
  hypotheses and do not supply such an implication automatically.
* Perron--Frobenius, Courant--Fischer, Gershgorin, Minkowski, LLL,
  Siegel, condition numbers, compound matrices, and Plucker relations:
  give valid metric or algebraic constraints when their hypotheses hold.
  The exact F calculation above keeps their relevant inverse-matrix cost
  visible. Rank and real spectral growth alone do not bound primitive
  gcd savings or establish a favorable rate for F applied to the actual pair.
* Contraction, Fredholm, spectral projections, Hilbert--Schmidt bounds,
  and semidefinite certificates: need a concrete operator, invariant
  region, or quadratic inequality for this family. No contracting operator
  or invariant certificate with the required exponent has been established.

The selected route is direct analysis of the rational map F and the
actual pair, followed by factorial/minor estimates with explicit local
divisibility. Its operator part is now exact. Its arithmetic asymptotic
part remains open in this project. The list offers possible tools; it
does not imply that one must meet the required exponent.

## Verification scope

`scripts/exact_transition_norm.py` checks eighteen transferred pairs at
weights 5,7,9 across nine coefficient matrices, entirely in rational
arithmetic. It independently reconstructs F, checks the operator bounds,
compares J to the previous transfer calculation, and checks the directional
certificate. These are finite verifications, not extrapolations. The
operator and convexity proofs in this note are not yet formalized in Lean.
