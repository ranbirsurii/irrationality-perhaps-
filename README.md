# Odd zeta formalization

This project formalizes exact algebraic pieces from both supplied chat texts,
plus the integer-smallness argument needed for an irrationality proof.

## Formalized from the chat texts

`OddZeta/AperyStructure.lean` verifies the symmetric-square coefficient
identities for the displayed Apéry root equation, the level-six branch values
`17 ± 12√2`, and the rescaling of the gauge-transformed equation under
`t = 9r`. It also records the three rational coefficients of the displayed
complete third-kind Picard–Fuchs operator.

`OddZeta/AperyFive.lean` defines the finite rational functions `F_n(t)` and
`R_n(t,z)` and proves that their numerator zeros at `1,…,n` persist for every
`z`. It defines the stated Apéry coefficients `A_n`, harmonic numbers,
`eta_(n,k)`, and the explicit formula for `C_n`; proves `A_1 = 5` and
`C_1 = -36`; and verifies the `n=1` forms and the scalar elimination identity
that cancels the `zeta(3)` term. It also gives explicit finite harmonic-sum
formulas for the rational terms `b_n` and `E_n` by computing the local Laurent
coefficients of the rational kernel; these yield `b_1 = 12` and `E_1 = 64`.
The identity for `C_n` is proved again from the second-order Laurent
coefficient. The Adams projector is formalized on a rational vector space and
on the specified weight decomposition: it kills weight 3, fixes weight 5,
and sends a rational weight-0 coordinate to `-7/24` of itself. Thus the
projected period in the formal weight model is `-4 A_n zeta(5) - 7 E_n/24`.
The coefficient `-4 A_n` is proved integral; Lean defines the exact reduced
denominator of `7 E_n/24` and proves that it clears the rational term.

The supplied text states that partial fractions of the infinite series produce
the displayed coefficients. Lean formalizes their finite Laurent/harmonic
algebra, but does not yet prove termwise differentiation and summation of the
infinite series. Likewise, the third-kind operator coefficients are recorded,
but the analytic proof that the integral satisfies the operator is not
formalized here. The weight-space calculation proves the projector once the
specified Adams eigenspace decomposition is given; it does not itself show
that the geometric Apéry family realizes that decomposition.

## Conditional irrationality step

`OddZeta/IrrationalityCriterion.lean` proves that integer-valued multiples
of a nonzero rational linear form cannot converge to zero. It also proves
that explicit bounds `q_n ≤ C exp(beta n)` and
`|L_n| ≤ C' exp(-alpha n)` imply `q_n L_n → 0` when `alpha > beta`.
The manuscript slopes are formalized as
`alpha_n = 4n log(1+sqrt(2))` and `beta_n = 2n+1`; Lean proves their gap is
positive for every `n ≥ 1`.

The manuscript's separate large-`N` construction states the target denominator
rate `kappa_n <= 2n+1` and decay rate
`alpha_n = 4n log(1+sqrt(2))`. The slope gap is now proved, and the generic
Lean theorem turns matching exponential bounds into the required convergence.
The source does not identify its finite-`N` forms with the chat's `R_n(t,z)`
family, so those bounds and nonvanishing still need to be proved for the
concrete deformed and projected forms. The elliptic chat gives the
characteristic formula once the marked point is specified, while leaving the
inhomogeneous regulator calculation as the next step. These statements remain
the status of the chat-derived construction in this project.

## Joint estimate audit

The joint estimate audit is in [ESTIMATE_AUDIT.md](ESTIMATE_AUDIT.md). For the
specific displayed weight-coordinate form `F_n=-4A_n zeta(5)-7E_n/24`, its
weighted harmonic-sum analysis gives

`E_n/A_n -> 4 zeta(5)+8 zeta(2) zeta(3)` and

`F_n/A_n -> -(31 zeta(5)/6+7 zeta(2) zeta(3)/3)`.

Thus this particular projected form has eventual same-sign coefficients and
cannot supply small integer forms, even after arbitrary common-factor
cancellation. `AperyEstimateAudit.lean` checks the consecutive-weight identity,
the weighted local algebra, `A_n>=1`, and the sign/normalization bounds. The
concentration and asymptotic limit proofs are written in the note and are not
yet formalized in Lean.

The note also tests a genuine integer/half-integer sampling replacement, an
explicit kernel whose numerator vanishes on both grids, and its combined
analytic/arithmetic budget. The script `scripts/joint_estimate_audit.py` gives
reproducible exact rational interval checks of four candidate normalizations.
Finite tests are kept separate from the asymptotic claims.

`AperyHankel.lean` supplies a different target-isolation mechanism: determinants
of the moments `zeta(5)-H_(a+k)^(5)` are affine in `zeta(5)`, with rational
coefficients, because the constant part of their matrix has rank one. Lean
proves this determinant identity over arbitrary commutative rings and checks
the rational/real specializations. A positive moment-integral argument in the
audit note gives nonvanishing. Exact finite tests of the primitive integer
forms, including shifts proportional to the matrix size, still give a
negative combined budget. This is a structural alternative to the displayed
projection, with an explicit arithmetic obstacle rather than an assumed
preservation of decay.

## All-weight determinant arithmetic

`OddZeta/OddHankelArithmetic.lean` is a self-contained Mathlib-based file for
every integer weight. It constructs integer coefficients for
`lcm(1,...,a+2N-2)^(sN) det[zeta(s)-H_(a+i+j)^(s)]`, proves the exact
prime valuations and an elementary logarithmic lower bound for that scale,
and verifies division by a certified common divisor. The irrationality
criteria explicitly require decay and arbitrarily late nonvanishing.

The derivational note in `notes/odd-zeta-arithmetic.tex` and its rendered PDF
prove positivity and the fixed-shift determinant asymptotic
`log(Delta)/N^2 -> -log(4)` on paper. They show that the uniform lcm
normalization grows for every integer `s>1`; this does not exclude sufficient
primitive gcd cancellation. The moment integrals and asymptotics are not
formalized in Lean. No unconditional all-odd irrationality theorem is claimed.

`scripts/sparse_hankel_audit.py` performs 700 exact small-space checks and 60
larger sparse/consecutive family checks at weights 3, 5, 7, and 9. Every larger
tested form has primitive absolute value greater than one. These finite
computations do not settle asymptotic smallness for other spaces.

## All-weight Adams projector

`OddZeta/AdamsGeneral.lean` formalizes the projector proposed in the chat texts.
For target weight `2r + 1`, it uses the Lagrange polynomial

`P_r(X) = prod_{1 <= j < r} (X - 2^(2j+1)) / (2^(2r+1) - 2^(2j+1))`.

Lean proves the eigenvalues are strictly increasing, the denominator is
nonzero, the projector kills every lower odd weight, fixes the target weight,
and gives the exact rational coefficient on the weight-zero coordinate. This
coefficient is fixed for each target weight and independent of the Apéry index.

## Hodge-circle and étale weight bookkeeping

`OddZeta/HodgeEtaleWeights.lean` records the realization data for a Tate
graded piece `Q(m)`: Hodge type `(-m,-m)`, weight-cocharacter exponent `-2m`,
étale cyclotomic exponent `m`, and Adams weight `m`. It proves that the Hodge
circle has exponent zero on every Tate twist, so the circle alone cannot
separate the odd-zeta weights. The weight cocharacter does separate them; the
étale and Adams exponents record the same twist index. These are realization
identities, not evidence that the Apéry family maps to such a Tate class.

For each proposed weight `2r+1`, the same file records the Hodge-circle spectrum
`2r, 2r-2, ..., -2r` on the candidate `Sym^(2r) H^1(E)`. It proves the action
is nontrivial for `r ≥ 1`, identifies the zero middle character, and records
the trivial circle character on the residue Tate graded line of the affine
curve `E \\ {O,P}`. This is the associated-graded weight calculation for the
marked affine elliptic curve, not a construction of its regulator class from
`R_n(t,z)`.

## Apéry K3 regulator source calculation

`OddZeta/AperyRegulatorGeometry.lean` records the coefficients of the
inhomogeneous Picard--Fuchs operator for the Apéry K3 normal function and
formalizes a source-side bound for its first forcing coefficient. The central
binomial estimate gives

`binom(2n,n)^2 / (16^n n(2n+2)) ≤ 1/n - 1/(n+1)`.

Consequently the rational partial forcing coefficients are monotone and lie
between 10 and 15; their real sequence converges by monotone bounded
convergence. This checks positivity and convergence for Kerr's K3 forcing
series. It is not a comparison theorem identifying that normal function with
the deformed Apéry kernel or the odd-zeta forms in the chat. No regulator
pairing with `zeta(2r+1)` is obtained from this estimate.

`OddZeta/AperyRegulatorComparison.lean` now gives the operator-level
identification explicitly. It writes the universal `X₁(6)` Weierstrass cubic
and verifies its marked section, normalizes the elliptic Picard--Fuchs
coefficients to the level-six root equation, and computes directly on a
regulator Taylor jet `A + B t` that the coefficient of `t` in the Apéry K3
Picard--Fuchs residual is `B - 5A`. The forcing series bounded above is the
source's expansion for precisely this residual coefficient. Thus the
Picard--Fuchs “identifier” is now an exact operator calculation, with an
explicit elliptic section as input data.

The same file now carries out an explicit algebraic bridge on the elliptic
fiber. If `α, β` are distinct nonzero roots of `x² + A(t)x + t`, it uses
`z = β(x-α)/(x(β-α))`, with inverse `x = α/(1-λz)` and
`λ=(β-α)/β`. Lean verifies the marked section's Legendre coordinate
`ν=(β-1)/(β-α)` and the transformed cubic, including its twist factor. I
also used the chat's explicit one-motive cycle identity `[P]-[O]`: Lean
models this degree-zero cycle, computes its Abel sum as `P`, and checks the
finite-pole coefficients of the algebraic third-kind candidate
`(Y+κ) dx/(2(x-ν)Y)`. Its coefficient is `+1` at `P` and vanishes at the
conjugate point, unlike the bare Legendre-Π differential, whose pole divisor
is symmetric. The cycle computation is an abstract additive-group model; it
does not establish the geometric identification `Pic⁰(E) ≃ E` for this
family. The remaining `-1` residue at `O` follows only after proving the local
expansion at infinity (or invoking and formalizing the global residue theorem);
that step and the relative de Rham/Abel--Jacobi comparison are still open.

The induced-map calculation is now explicit: `cycleAbelSum_inducedMap` proves
that an additive realization homomorphism commutes with Abel summation, and
`markedAbelCycle_inducedMap` sends `[P]-[O]` to the image of `P`. This is the
functoriality law an induced morphism must satisfy. It does not manufacture the
needed correspondence out of the Apéry family. A Mayer--Vietoris/groupoid
construction is a plausible way to assemble local horizontal maps into such a
global correspondence, but it still has to produce those maps and preserve
the marked residue data.

The induced differential-module map is now explicit as well. On the open set
where its denominators do not vanish, the base change is
`x = r(1-9r)/(1-r)`, with formal derivative expressions
`x' = (1-18r+9r²)/(1-r)²` and `x'' = -16/(1-r)³`. Substituting these into
the pullback of the Apéry root equation gives coefficients
`(18r-1)/(r(9r-1))` and
`(10-11r+9r²)/(4(r-1)² r(9r-1))`. The gauge logarithmic derivative is
`h = 1/(2(r-1))`; Lean proves that the transformed coefficients
`P + 2h` and `Q + Ph + h' + h²` are exactly `levelSixGaugeP` and
`levelSixGaugeQ`. Those coefficients are the level-six elliptic root
Picard--Fuchs equation after `t=9r`. Thus the rank-two solution equations
are related by an explicit base-change-and-gauge map; the earlier symmetric
square calculation then gives the standard rank-three Apéry operator.

There is a coefficient discrepancy that must be tracked explicitly. The
standard Apéry Euler operator has `3x(x-17) theta²`, whereas the operator
printed in [Kerr's two-cycles paper](https://www.math.wustl.edu/~matkerr/TwoCycles091712.pdf)
and encoded here has `2x(x-17) theta²`. Lean now proves the exact defect
`L_standard f = L_Kerr f + x(x-17) theta² f`. Thus an inhomogeneous source
must receive that correction when changing between these encoded operators.
The root-equation calculation alone does not identify their normal functions.

This closes the operator-coefficient comparison, not the arithmetic theorem.
The derivative expressions are supplied as rational formulas in Lean and the
coefficient identities are proved algebraically; real-analytic derivative
and square-root branch statements are not formalized. More substantially,
the map has not been lifted to a morphism of the inhomogeneous normal-function
extensions, nor paired with an integral cycle to produce integer linear forms
in `ζ(2r+1)`. The next rigorous step is to construct that extension morphism
and compute its period pairing. Until it yields certified nonzero integer
forms with denominator growth slower than their decay, the conditional
irrationality criterion below cannot be applied.

There is also a direct arithmetic checkpoint. The January 2026, unreviewed
preprint *On the Irrationality of the Odd Zeta Values* claims irrationality
for every odd zeta value. Its parameter selection requires
`g(α) = 1 + q + λα - γ_q(α) < 0`, with `λ=2n+3`. For `λ≥5`, this inequality
cannot hold: if `q+1≤exp(λ)`, convexity and `g'(0)≥0` give `g(α)≥1+q`; if
`q+1>exp(λ)`, the unique minimum is at
`α*=q/(exp(λ)-1)-1`, where
`g(α*) = q(1+log(1-exp(-λ))) + 1-λ+log(q+1) + q log(1+1/q) > 0`.
Thus that version's parameter lemma does not establish the required decay for
the odd-zeta cases. This audit is not a proof that no corrected argument can
work; it prevents us from importing an invalid estimate as a shortcut.

The geometric and arithmetic paths now have clear independent targets. The
geometric target is an actual horizontal correspondence, constructed by local
maps and overlap cocycles. The arithmetic target is an explicit sequence of
integer forms `A_m ζ(2n+1)-B_m` with certified nonvanishing and decay. Neither
target follows from the other, and both are needed for an unconditional
all-odd irrationality proof.

This is still a Picard--Fuchs and fiber-coordinate model. It does not construct
the horizontal correspondence from the chat's deformed kernel to Kerr's K1
cycle, nor identify the normalized third-kind differential and its period with
that cycle's normal function. Those are actual geometric/regulator comparison
claims, not consequences of equality of operator ranks or one Taylor
coefficient.

## Bridge approaches considered

The ten strongest next methods, ranked for the data actually available here,
are as follows. The ranking is a choice of research route, not a theorem that
the methods will prove irrationality.

| Rank | Method | Concrete calculation required |
| --- | --- | --- |
| 1 | All-order deformation and creative telescoping | Construct every `z` coefficient of the actual kernel and its forced extension equation. Implemented below. |
| 2 | Inhomogeneous companion-system map | Extend the homogeneous gauge matrix and match the entire forcing vector. |
| 3 | Formal recurrence and boundary uniqueness | Show a proposed pushforward agrees with the uniquely specified local solution. Implemented for the kernel tower below. |
| 4 | Relative de Rham residue sequence | Construct the class of the marked third-kind differential and its boundary map. |
| 5 | Modular expansion comparison | Match the normalized full expansions of the periods and sources at a cusp. |
| 6 | Kummer or Shioda-Inose correspondence | Give equations for the correspondence and transport the marked cycle. |
| 7 | Picard-Lefschetz thimble pushforward | Transport the actual integration chain and compute its boundary contributions. |
| 8 | Elliptic-polylogarithm residue comparison | Match the class, including the kernel invisible to residues. |
| 9 | Adams action on a constructed extension | Prove that the geometric action induces the proposed eigenspace decomposition and preserves the required estimates. |
| 10 | Integral-lattice comparison | Transport a specified integral class and calculate its denominator after comparison. |

The selected route now has a construction in `OddZeta/AperyDeformation.lean`.
For each nonsingular rational parameter `t`, it constructs the formal Taylor
series of every finite kernel by multiplying explicit inverses of
`(t+j)²+z`. Both the formal kernel and the original rational `R_n(t,z)` satisfy
the same denominator identity, with numerator `aperyNumerator(n,t)²`.
Its coefficient of order zero is proved equal to the original `aperyF`.

Write `r_(n,m)` for the coefficient of `z^m` in that finite kernel and
`G_m(q)=sum_n r_(n,m) q^n`. With
`D_t=(theta+t)²-q(theta+1-t)²`, Lean proves at every order

`D_t G_0 = 1`, and `D_t G_(m+1) = -G_m`.

The induced lifting map is explicit. For any source `s(q)`, its coefficients
are constructed recursively by

`h_0=s_0/t²`,

`h_(n+1)=(s_(n+1)+(t-n-1)² h_n)/(t+n+1)²`.

Lean proves that this gives a rational linear map `H_t`, that
`D_t H_t(s)=s`, that `D_t` is injective on these formal series, and therefore
that `G_(m+1)=H_t(-G_m)` and the entire forced tower is unique. This constructs
the local formal extension at every deformation order. To use it for the
zeta linear forms, the residue or infinite-sum pushforward in `t` still has to
be computed and shown to transport the sources and the arithmetic estimates.

`OddZeta/AperyZetaPushforward.lean` now establishes the first analytic
pushforward for every deformation order. It identifies
`[z^m] R_0(t,z) = (-1)^m/t^(2m+2)`, proves its real derivative formula, proves
summability of the differentiated values at positive integers, and evaluates
their sum as `(2m+2)(-1)^m ζ(2m+3)`. This uses the convergent Dirichlet-series
definition of zeta in mathlib, without an irrationality assumption.

`OddZeta/AperyTelescoper.lean` gives explicit polynomial coefficients
`A(n,z), B(n,z), C(n,z)` and a quadratic certificate `P(n,z,t)` satisfying

`A R_(n+1)(t,z) + B R_n(t,z) + C R_(n-1)(t,z)`

`= P(t+1) R_n(t+1,z) - P(t) R_n(t,z)`.

The polynomial certificate and its application to the actual rational kernel
are both checked in Lean. Its coefficients at `z=0` reduce, after the common
factor `6n^4(n+1)^4`, to the usual Apéry coefficients
`-(n+1)^3`, `(2n+1)(17n²+17n+5)`, and `-n^3`. For nonnegative rational `z`,
the finite sum over `t=1,...,M` is proved to equal the single upper boundary
term `P(M+1) R_n(M+1,z)`; the lower boundary is zero. Passing the differentiated
and coefficient-extracted identity to an infinite sum, and bounding the
projected forms and their denominators, remain necessary for irrationality.

The candidate ways to connect the chat kernel to an Apéry regulator are:

1. Explicitly transform the marked `X₁(6)` section to Legendre coordinates.
2. Find a rational gauge transformation between the two scalar operators.
3. Construct an isomorphism of their first-order companion systems.
4. Compare local exponents and monodromy representations.
5. Match their modular Hauptmodul and theta-series expansions.
6. Build the relative de Rham residue sequence for `E minus {O,P}`.
7. Normalize the third-kind form using the theta/Poincaré biextension.
8. Identify the class with an elliptic-polylogarithm Eisenstein class.
9. Compute its Rankin--Eisenstein regulator pairing.
10. Construct the Apéry K3 higher-Chow cycle and its normal function.
11. Use a Kummer or Shioda--Inose correspondence to compare the K3 and elliptic motives.
12. Compare the classes through the elliptic-fibration Leray spectral sequence.
13. Match Picard--Lefschetz thimbles and vanishing cycles.
14. Compare limiting mixed Hodge structures at a cusp.
15. Prove uniqueness of the inhomogeneous solution from its boundary expansion.
16. Match boundary residues, then separately control the parabolic kernel.
17. Construct an algebraic correspondence and prove it is horizontal.
18. Compare integral lattices through `p`-adic/étale realizations.
19. Use Frobenius congruences and the Dwork unit-root splitting.
20. Apply creative telescoping to the actual `R_n(t,z)` kernel and compare its
    inhomogeneous equation and boundary values.

Approaches 1 and 20 are now implemented as explicit calculation stages.
Approach 1 gives the marked Legendre characteristic and transformed cubic.
For approach 20, `OddZeta/AperyFive.lean` proves the actual kernel recurrence

`R_(n+1)(t,z) = R_n(t,z) (t-n-1)^2 / ((t+n+1)^2+z)`

under its exact nonvanishing conditions. It then proves coefficientwise that
`G_(t,z)(q) = sum_n R_n(t,z) q^n` satisfies

`[((theta+t)^2+z) - q(theta+1-t)^2] G_(t,z) = 1`,

where `theta = q d/dq`; the initial coefficient is exactly
`R_0(t,z)=1/(t^2+z)`. The proof is entirely formal in `PowerSeries`, and a
positive-`t`, nonnegative-`z` theorem discharges the recurrence's denominator
conditions. This is a new exact equation for the chat kernel, not yet Kerr's
Apéry K3 equation: it differentiates in the generating variable `q`, while
the K3 Picard--Fuchs operator differentiates in the geometric base parameter.
The next concrete bridge is to prove that the actual residue/period pushforward
of this equation in `t` (and the deformation coefficient in `z`) yields the
K3 normal-function equation and its boundary data. That pushforward is not
proved here.

The Scholze-style p-adic route is not the needed bridge at this stage.
Perfectoid/pro-étale comparison theorems compare cohomology realizations for
specified p-adic analytic spaces; the diamonds six-functor formalism supplies
étale operations on those spaces. Neither theorem constructs the missing
cycle from `R_n`, identifies its complex regulator period, or forces this
generating-variable equation to become the K3 equation. A p-adic realization
could help after the algebraic cycle and its comparison map have been built.
The current bottleneck is the explicit residue/period pushforward, so the
formalization keeps its effort there rather than adding an unrelated p-adic
placeholder.

## What is still unproved in the chat construction

The two chat texts are the primary specification. The manuscript copy is only
a secondary aid and does not supply the missing bridges below.

The `n=0` infinite differentiated series has its all-order odd-zeta evaluation
proved. For general `n`, termwise deformation extraction, convergence, and
partial-fraction summation remain to be established for the actual `R_n(t,z)`
family. The finite telescoping certificate keeps its upper boundary term
explicit until those limiting steps are justified.

The geometric lift is not constructed. The chats propose a marked divisor on a
level-six elliptic family and a candidate complete third-kind period, but do
not identify the divisor's actual coordinate in that family or prove that the
resulting period is the regulator of the deformed Apéry coefficients. They
explicitly leave the pullback to the inhomogeneous Picard--Fuchs equation and
the regulator comparison as the next calculation. The separately formalized
Apéry K3 normal function supplies an actual regulator object and an explicit
inhomogeneous equation, but no morphism or cycle comparison has been proved
from it to the chat's deformed kernel.

The all-weight projector is proved as linear algebra, but its application to
the proposed zeta forms still needs a constructed class and a proof that the
class decomposes into the stated Adams eigenspaces. No such class or compatible
Adams action is defined in the supplied chats or in the manuscript aid.

Finally, the irrationality criterion is conditional on concrete projected
integer coefficients, arbitrarily-late nonvanishing, and denominator and decay
bounds. Those estimates have not been derived for the chat's projected forms.
Consequently, this repository does not claim a proof that every `zeta(2n+1)`
is irrational.

All Lean source files use ordinary visible code and contain no `sorry` or
`admit`.

