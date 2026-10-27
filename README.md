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

This is still a Picard--Fuchs and fiber-coordinate model. It does not construct
the horizontal correspondence from the chat's deformed kernel to Kerr's K1
cycle, nor identify the normalized third-kind differential and its period with
that cycle's normal function. Those are actual geometric/regulator comparison
claims, not consequences of equality of operator ranks or one Taylor
coefficient.

## Bridge approaches considered

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

Approach 1 is the implemented first bridge: it determines the marked
Legendre characteristic and exact transformed cubic by elementary algebra,
giving a concrete input to approach 6 or 7. The most decisive next test is
approach 20 on the actual chat kernel, followed by approach 17 or 10 to prove
that the resulting normal function is the Apéry K3 one. None of these
comparisons is presently asserted as proved.

## What is still unproved in the chat construction

The two chat texts are the primary specification. The manuscript copy is only
a secondary aid and does not supply the missing bridges below.

The finite rational formulas do not yet prove that the infinite differentiated
series has the stated zeta expansion: termwise differentiation, convergence,
and the partial-fraction summation remain to be established for the actual
`R_n(t,z)` family.

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

