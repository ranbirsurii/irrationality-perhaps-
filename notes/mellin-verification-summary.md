# Cofactor and Mellin verification, 27 October 2026

This is a research development, not a proof that all odd zeta values are
irrational. The quantitative primitive-height or polynomial-smallness
estimate is still unproved.

The three added modules compiled with Lean 4.34.0-rc2, the matching pinned
mathlib, and `relaxedAutoImplicit=false`:

- `OddZeta/CofactorArithmetic.lean`
- `OddZeta/MellinRationalMoments.lean`
- `OddZeta/PolynomialSmallnessCriterion.lean`

The 24 declarations listed by `scripts/AuditMellinAttack.lean` use only
`propext`, `Classical.choice`, and `Quot.sound`, as applicable. The output
is saved in `lean-mellin-verification.txt`. No project axioms or proof
placeholders were added.

The complete project entry point `OddZeta.lean` also compiled successfully
after the final cofactor additions. The paper compiled with both the desktop
editor and Tectonic; all seven final rendered pages were inspected. The
final TeX log has no overfull or underfull box warnings. The new Lean and
TeX sources contain no percent characters or hidden Unicode formatting
characters.

The cofactor module proves the affine expansion, the lower-row kernel
identity, divisibility by the cofactor content, and the exact factorization
of the full coefficient gcd. The Mellin module proves partial fractions,
the zero residue sum, an explicit harmonic-tail remainder bound, its limit,
the corresponding `HasSum` statements, the real Riemann-zeta evaluation,
toric contiguity, and pole cancellation. The polynomial module proves the
rational evaluation gap and the conditional irrationality criterion.

The paper supplies separate proofs of the integral interpretation,
positivity, determinant degree, Chebyshev bound, rowwise denominator
budget, and uniform endpoint calculation. Those arguments are not claimed
to be formalized by these Lean modules.

The exact arithmetic audits succeeded:

- `primitive_height_attack.py`: 12 cases, weights 3, 5, 7, 9 and sizes
  30, 40, 60. Its rowwise construction also agrees with all 12 older
  rational coefficient certificates.
- `balanced_mellin_audit.py`: 57 balanced and toric spaces, weights
  3, 5, 7 and sizes up to 21. Exact slope ranks certify the degree upper
  bounds; integer interpolation, an extra determinant evaluation, full
  coefficient gcd reduction, and rational interval evaluation are checked.
- `multiple_mellin_audit.py`: 32 pure-target linear forms at weights
  3, 5, 7, 9 through index 40.
- `cofactor_content_audit.py`: 12 exact cofactor vectors, checked against
  `B c = det(B) e_0` and the affine coefficient formulas.

All tested alternative primitive absolute evaluations exceed one. This
finite observation is not an asymptotic impossibility theorem.

The scripts use only Python 3.11 or newer and its standard library.
Sign and comparison certificates use exact integers and rational intervals;
floating-point logarithms are descriptive columns only.

For a fresh checkout with the pinned Lean toolchain, run:

```text
lake exe cache get
lake build
lake env lean scripts/AuditMellinAttack.lean
python scripts/primitive_height_attack.py --output primitive-height-attack.json
python scripts/balanced_mellin_audit.py --output balanced-mellin-audit.json
python scripts/multiple_mellin_audit.py --output multiple-mellin-audit.json
python scripts/cofactor_content_audit.py --output cofactor-content-audit.json
```

The source paper is `arithmetic-saturation-note.tex`. Its author field is
blank; authorship and submission metadata have not been supplied. The
arXiv-style source package contains that single main TeX file, ancillary
Lean/Python sources, exact data, and verification records. It is a draft
source package and has not been submitted to arXiv.
