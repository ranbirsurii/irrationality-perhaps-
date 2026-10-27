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
inhomogeneous regulator calculation as the next step. The project therefore
does not claim irrationality of `zeta(5)` or of every odd zeta value.

All source files use ordinary visible Lean code and contain no `sorry` or
`admit`.
