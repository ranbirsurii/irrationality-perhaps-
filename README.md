# Odd zeta formalization

This Lean project formalizes the integer-smallness contradiction used in an irrationality argument and exact algebra from the supplied Apéry/elliptic-integral note. It provides a conditional application to `Re(ζ(2k+1))`.

For `Δ = x² - 34x + 1`, the file `OddZeta/AperyStructure.lean` writes the quotient-rule expressions for the derivatives of

`u'' + ((2x² - 51x + 1)/(xΔ)) u' + ((x - 10)/(4xΔ)) u = 0`

and verifies the resulting symmetric-square coefficient identities: `3p`, `(1 - 112x + 7x²)/(x²Δ)`, and `(x - 5)/(x²Δ)`. These are the normalized ordinary-derivative coefficients of the Apéry operator. It also proves the level-six branch points and their values `17 ± 12√2`.

The theorem `oddZetaValue_irrational_of_small_linear_forms` assumes precisely: (i) a nonzero integer multiplier `q n` at every index, (ii) nonzero linear forms arbitrarily far out, and (iii) convergence of `q n * (A n * Re(ζ(2k+1)) - B n)` to zero. In the manuscript's asymptotic formulation, the claimed inputs are the nonvanishing finite-`N` forms, the decay rate `liminf -N⁻¹ log |Lₙ,ₙ| = 4n log(1+√2)`, and the common-denominator bound `limsup N⁻¹ log qₙ,ₙ ≤ 2n+1`; these rates are intended to imply (iii). They are not proved by the pasted period calculations, so the formalization does not assert irrationality of all odd zeta values.

The code is written as ordinary visible Lean source and contains no `sorry` or `admit`.
