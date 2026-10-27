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
that cancels the `zeta(3)` term. The Adams projector is formalized as its
rational eigenvalue polynomial: it kills eigenvalue `8`, fixes `32`, and
scales eigenvalue `1` by `-7/24`.

The source gives only existence of rational terms `b_n` and `E_n` in the two
forms, not a general formula for them, so Lean keeps them as rational inputs.
The displayed `L_(n,0)` and `L_(n,1)` coefficient identities are recorded as
definitions; the source text calls them the result of the Apéry/partial-
fraction calculation but does not supply that derivation. Likewise, the
third-kind operator coefficients are recorded, but the analytic proof that
the integral satisfies the operator is not formalized here. The generic
linear-operator lemma proves the Adams projector kills a weight-3 eigenvector
and fixes a weight-5 eigenvector; it does not produce the proposed regulator
class or show that the Apéry family maps to it.

## Conditional irrationality step

`OddZeta/IrrationalityCriterion.lean` proves that integer-valued multiples
of a nonzero rational linear form cannot converge to zero. Its odd-zeta
corollary still requires nonvanishing and denominator-scaled convergence.

The manuscript's separate large-`N` construction states the target rates
`alpha_n = 4n log(1+sqrt(2))` and `kappa_n <= 2n+1`, with the gap
`alpha_n - kappa_n >= 4n log(1+sqrt(2)) - (2n+1) > 0`. Its odd-zeta theorem
assumes the uniform finite-`N` coefficient theorem that is supposed to supply
the forms, denominators, and nonvanishing. These rates concern that manuscript
construction; the text does not show that they apply to the chat's new
`R_n(t,z)` forms or to the proposed Adams-projected regulator form. The chat
texts themselves leave the marked-point characteristic and inhomogeneous
third-kind regulator equation as next calculations. Consequently this Lean
project does not claim irrationality of `zeta(5)` or of every odd zeta value.

All source files use ordinary visible Lean code and contain no `sorry` or
`admit`.
