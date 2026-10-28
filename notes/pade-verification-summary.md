# Symmetric Padé verification, 27 October 2026

This development constructs exact odd-zeta cancellation mechanisms. It does
not prove irrationality of every odd zeta value or a sequence of primitive
forms tending to zero.

Five added Lean modules compiled under Lean 4.34.0-rc2 and matching pinned
mathlib, with `relaxedAutoImplicit=false`:

- `OddZeta/RationalCentering.lean`: denominator divisibilities and bounds
  under rational subtraction, invariance under integer subtraction, and
  invariance of the coefficient ratio's denominator under common scaling.
- `OddZeta/SymmetricPadePeriods.lean`: residue-sum cancellation, finite
  period-coordinate elimination, two explicit rational partial-fraction
  identities, the actual Riemann-zeta `HasSum` identity for
  `112*zeta(5)-107`, and its lower bound of 5.
- `OddZeta/PoisedKernelPositivity.lean`: the actual rational kernel is zero
  at positive integers up to the numerator block length and positive
  thereafter; any convergent sum of its integer values is positive.
- `OddZeta/PadeNormalizedElimination.lean`: rational lower-period nullvector
  existence, normalization to sum of absolute weights one, preservation
  of cancellation, the resulting bound, and a convergence implication.
- `OddZeta/PadeCombinedFive.lean`: the explicit positive combination
  `601088*S_(2,2,2)+37632*S_(2,2,3)`, its factored rational kernel,
  full partial fractions, actual `HasSum` identity giving
  `91776*zeta(5)-95165`, and strict positivity of that sum.

The general gamma-ratio representation, Barnes contour identity, polylog
differential equation and indicial calculations, Taylor-jet formula,
functional Padé identity, and asymptotic saddle-rate theorem are paper
proofs. One-sign finite combinations have analytic nonvanishing by
the positive-kernel argument. Producing such subsidiary-condition vectors
with a winning size bound for unbounded indices is unproved.

The symmetric audit passed all 92 cases at weights 3, 5, 7, 9 and indices
1, 2, 3, 5, 8, 12, 20. It constructs local Taylor coefficients with exact
rational arithmetic, checks reflection, reconstructs sample rational
function values, verifies subsidiary-condition rank and cancellation,
clears all coefficient denominators, removes the complete gcd, and
evaluates the result in rational zeta intervals. Of the 46 well-poised
cases, 34 have one-sign combination weights.

The separate profile search enumerates all two-kernel block-length pairs
in the stated proper-rational range at indices 2, 4, 8, 12, 20 for zeta(5).
It produces 2140 distinct nonzero-target primitive pairs. Rational intervals
certify the unique best absolute value among each finite candidate set.
The five selected profiles all have one-sign weights. Only the first two
selected forms have absolute value below one. This finite search proves no
asymptotic optimality or impossibility result.

The analytic calculation gives an exact term ratio and a unique saddle for
each fixed `0 < beta < s/2`. A finite tail estimate bounds the whole positive
sum by `(2K+1)` times its largest term, with `K=O(n)`. Elementary factorial
estimates then prove the logarithmic rate limit. At weight 5 with `m=n`,
the rate is in `(-4.970794,-4.970793)`. This proves decay for the stated
normalized individual sums, before final integer normalization.

A pointwise comparison of the rate function at beta=1 gives an all-weight
analytic conclusion: its maximum decreases as the odd weight increases,
and the certified weight-3 maximum is less than -1.99. For each fixed odd
weight s>=3 the normalized individual sums with m=n are therefore at most
exp(-1.99*n) for all sufficiently large even n. This is a paper proof;
it does not include the primitive arithmetic cost.

For fixed weight s=2r+1, the r normalized sums with m=n-j, 0<=j<r,
all have the same rate limit. Their r-1 lower-period equations always
admit a nonzero rational vector. Dividing it by the sum of its absolute
entries preserves the equations and bounds the resulting pure-target
rational form by exp(-1.99*n) for sufficiently large even n. Lean proves
the linear algebra and bound-preservation implication. Nonvanishing and
decay after primitive integer normalization remain unproved.

The analytic audit certifies 44 saddle roots and negative rate intervals
using rational bisection and rational logarithm enclosures. It also checks
22 exact positive-sum intervals against independent period intervals.
The functional audit verifies the numerator zeros underlying the high-order
Padé remainder at zero; the coefficient conditions at one remain exact.

The profile data include the coefficient content removed after the integer
combination, as well as oriented weights on the primitive full-period rows.
The exact identity is that the integer combination equals that content
times the final primitive target/constant row.

Reproduce the arithmetic with Python 3.11 or newer and its standard library:

```text
python scripts/symmetric_pade_audit.py --output symmetric-pade-audit.json
python scripts/pade_profile_search.py --output pade-profile-search.json
python scripts/analytic_sum_control.py --output analytic-sum-control.json
```

Rebuild with the pinned Lean toolchain:

```text
lake exe cache get
lake build
lake env lean scripts/AuditSymmetricPade.lean
```

The 29 foundation reports are saved in `lean-pade-verification.txt`.
They contain only standard Lean foundations and no `sorryAx`.
No project axioms or proof placeholders were added. The new Lean and TeX
sources use visible ordinary text without percent characters or hidden
Unicode formatting characters.

The complete Lean entry point compiled after the final module additions.
The six-page paper compiled with both the desktop editor and Tectonic.
All six final rendered pages were inspected, and the final log contains
no overfull or underfull box warnings.

The source paper is `symmetric-pade-note.tex`. Its author field is blank.
The supporting source bundle is a research draft and has not been submitted
to arXiv.
