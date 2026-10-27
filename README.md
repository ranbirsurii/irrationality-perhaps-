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
the regulator comparison as the next calculation.

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

