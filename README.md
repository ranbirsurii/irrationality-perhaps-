# Odd zeta formalization

This Lean project formalizes the integer-smallness contradiction used in an irrationality argument and exact branch algebra from the supplied Apéry/elliptic-integral note. It provides a conditional application to `Re(ζ(2k+1))`.

The theorem `oddZetaValue_irrational_of_small_linear_forms` assumes precisely: (i) a nonzero integer multiplier `q n` at every index, (ii) nonzero linear forms arbitrarily far out, and (iii) convergence of `q n * (A n * Re(ζ(2k+1)) - B n)` to zero. In the manuscript's asymptotic formulation, the claimed inputs are the nonvanishing finite-`N` forms, the decay rate `liminf -N⁻¹ log |Lₙ,ₙ| = 4n log(1+√2)`, and the common-denominator bound `limsup N⁻¹ log qₙ,ₙ ≤ 2n+1`; these rates are intended to imply (iii). They are not proved by the pasted period calculations, so the formalization does not assert irrationality of all odd zeta values.

The code is written as ordinary visible Lean source and contains no `sorry` or `admit`.
