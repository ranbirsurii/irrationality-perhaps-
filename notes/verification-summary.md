# Verification record, 27 October 2026

All six new Lean modules compiled successfully with Lean 4.34.0-rc2,
the matching local mathlib, and `relaxedAutoImplicit=false`:

- `OddZeta/GcdDecalage.lean`
- `OddZeta/IntegralFramedComparison.lean`
- `OddZeta/AperyModernIdentification.lean`
- `OddZeta/AperyFormalPeriod.lean`
- `OddZeta/HankelEndpointEstimates.lean`
- `OddZeta/RowwiseHankelArithmetic.lean`

The complete project entry point `OddZeta.lean` was checked successfully
after these module builds. The 33 reports from
`scripts/AuditGcdDecalage.lean` contain only the standard Lean foundations
`propext`, `Classical.choice`, and `Quot.sound`, as applicable. They contain
no `sorryAx`. The reports are saved in `lean-integral-verification.txt`.
No project axiom declarations or proof placeholders were introduced.
The new Lean and TeX sources contain no percent comments or hidden Unicode
formatting characters.

The exact rational coefficient audit passed all 12 weight/size choices.
It checks the primitive row, the rowwise common divisor, the residual gcd,
and the extracted local torsion factors. The endpoint audit passed all
24 weight/size/shift choices against rational zeta enclosures.
The complete data are saved in `coefficient-chain-audit.json` and
`endpoint-error-audit.json`. These finite computations are distinct from
the asymptotic paper proofs.

The TeX source compiled successfully both in the desktop editor and with
Tectonic. All seven rendered pages were inspected. There are no overfull
or underfull box warnings in the final TeX log.

The Schur-complement, Jacobi-integral, determinant-asymptotic, and limit
arguments are mathematical proofs in the note, not Lean-verified theorems.
No integral geometric identification or sufficient primitive-height bound
for every odd weight has been proved. The all-odd irrationality conclusion
is not claimed.
