# Uniform-cost research and formal verification

28 October 2026. Research began at 20:32:07 UTC. The fifty-route comparison
is `notes/fifty-uniform-cost-strategies.md`.

## Proved additions

The existing manuscript now contains three additional propositions:

1. Exact integer minimum certificates for the primal and dual binary forms,
   giving optimal squared cost nu/delta^2 and the sharp comparison
   H^2/mu <= nu/delta^2 <= 4H^2/(3mu).
2. A uniform Laurent-coefficient envelope and an all-index Cramer-vector
   cost envelope for the actual consecutive-block family.
3. A common lower-row prime divisor at every odd weight:
   product_(n<p<=(s-2)n/(k-1)) p divides d_n^(s-k) a_k(n,m).
   It holds for every block 0<=m<=n. Dividing the lower rows by these
   factors improves the all-index cost envelope. At weight seven the
   upper exponent improves by exactly 7/4.

A central-binomial majorant further sharpens the coefficient exponent to
(s-2)log(2)+3log(3), saving another (r-1)log(32/27) in the cost envelope.
Its proof is included in the manuscript and the independent exact checks.

The last two envelopes do not satisfy the required arithmetic budget.
The sharper reduced-form family estimate remains unproved. Consequently
no unconditional irrationality theorem for all odd zeta values, or for
an individual new odd zeta value, is asserted.

## Lean scope

Five new modules contain thirty-two proved theorems:

- `BinaryGaussMinimum.lean`: nine integer minimum and transference results.
- `DualCoefficientGram.lean`: seven determinant, adjugate, and positivity results.
- `BinaryGaussCertificate.lean`: five soundness and attainment results for
  arbitrary integer unimodular reduction witnesses.
- `CramerKernelEnvelope.lean`: five determinant row bounds, exact cancellation,
  mass bounds, and free-coordinate independence results, in arbitrary dimension.
- `FiniteFieldTranslationTrace.lean`: six finite-field trace, coefficient
  vanishing, composition, and degree-inequality results.

All five modules compiled with exit code zero using the pinned Lean
4.34.0-rc2 compiler and cached matching mathlib. The combined driver
`VerifyBinaryGauss.lean` also compiled with exit code zero. Its thirty-two
printed dependency sets in `binary-gauss-axioms.log` contain only
propext, Classical.choice, and Quot.sound, as applicable. None uses a
new mathematical axiom, sorryAx, or a native-decision axiom.
The complete `OddZeta.lean` library entry point also compiled with exit
code zero after all five new modules were exported. Unchanged modules
were imported from their existing matching compiled objects.

The actual Laurent-product majorization, the identification of the
finite-field trace with these rational kernels, the prime number theorem
application, and the Euclidean lattice realization remain paper proofs.
The full formalized growth estimate requested by the user is not present.

## Independent exact checks

`scripts/check_uniform_prime_envelope.py` completed successfully:

- Seven cases at weights five, seven, nine, and eleven.
- All block lengths at each selected index.
- Two independent coefficient algorithms agree exactly as rational numbers.
- 226 coefficient-envelope checks and 506 prime-divisibility checks.
- 70 full finite-field polynomial trace identities, computed directly from
  the polynomial product and checked against the independent Laurent data.
- Exact Cramer cancellation vectors and their divisor-refined mass bounds.

These check the implementation. The manuscript's all-index proofs do not
rely on extrapolating them.

An additional independent normalization check reuses the existing
weight-five records at indices 20, 80, and 1280. Inverting the full
augmented matrix by integer adjugate columns and reducing its primal
Gram form gives exactly the same optimal squared cost as the saturated
kernel and dual-form construction. This check is reproduced by
`scripts/check_dual_cost_reduction.py`; it adds no family indices and
supplies no asymptotic extrapolation.

## Manuscript and rendering

The existing `main.tex` was edited in place and successfully checked with
the desktop editor's built-in compiler after the new proofs were added.
No separate PDF was compiled or exported. The old committed ten-page PDF
remains explicitly labelled an older snapshot; it is not the current paper.
The current live editor preview is generated from the revised source.
