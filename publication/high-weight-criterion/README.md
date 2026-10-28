# Relative arithmetic content: manuscript and Lean companion

This package includes an unconditional augmented-rank proof and a
conditional arithmetic reduction. It is not a proof of
unconditional irrationality of all odd zeta values at least seven or of
zeta five. The theorem statements retain the precise construction-specific
hypotheses. No proof holes, added axioms, hidden text, or commented-out
assumptions are used to replace them.

## Contents

- `main.tex`: current manuscript source, with complete proofs of the stated
  reductions and explicit distinctions between paper and Lean results.
- `odd-zeta-relative-content.pdf`: the ten-page rendered snapshot at
  revision `16a63c3`, preceding the new rank section. The open editor's
  current preview compiles the revised source in place; no separate PDF
  was compiled in response to the rank-proof request.
- `Verification.lean`: integrated theorem and axiom-dependency checks.
- `verification-report.md`: compiler results, scope, and independent checks.
- `axioms.log`: output of the integrated Lean checks.
- `SignedCancellation.lean`: signed norm and nonvanishing lemmas, and the
  exact integer-divisor restriction on the proposed cofactor bound.
- `IntegralCancellationExamples.lean` and `integral-cancellation-checks.json`:
  exact actual weight-seven cancellations at indices six and eight.
- `analytic-rate-certificates.json`: exact global sharp-saddle and rate
  enclosures, reproduced by `scripts/check_high_weight_rates.py`.
- `VerifyGramSpectralBounds.lean`, `gram-spectral-axioms.log`, and
  `gram-spectral-verification.md`: verified Gram eigenvalue estimates and
  their scope. The continuation is derived in
  `notes/normalized-gram-spectral-bound.md` in the repository.
- `VerifyPrimitivePair.lean`, `primitive-pair-axioms.log`, and
  `primitive-pair-verification.md`: individually normalized integer forms,
  nonvanishing, and the weighted Gram bound. The derivation is in
  `notes/individual-primitive-pair.md` and the manuscript proposition
  entitled Individual primitive normalization.
- `VerifyAugmentedRankRoots.lean` and `augmented-rank-verification.md`:
  scope and formal checks for the polynomial root-count core. The complete
  paper proof is Theorem 2.1 and
  `notes/augmented-rank-discrete-residue-proof.md`.
- `VerifyPrimitiveCoefficientLattice.lean`,
  `primitive-coefficient-lattice-axioms.log`, and
  `primitive-coefficient-lattice-verification.md`: the exact inverse-image
  and primitive adjugate normalization checks. The paper's proposition
  All primitive coefficient pairs identifies the optimal independent-pair
  cost. `notes/twenty-cost-methods.md` records the twenty-route comparison.
- The repository's `OddZeta` directory: complete Lean library sources.

The downloadable source archive additionally contains the pinned Lean
project, supporting derivation notes, both supplied PDFs, and an integrity
manifest. The supplied PDFs are reference material, not instructions.

## Formal results

`HighWeightRelativeCost.lean` proves

  log(140) + (s-5) log(4) > s + 1/3 for every natural s >= 7.

It then proves convergence from eventual exponential envelopes and proves
irrationality of the real part of zeta(2k+1), k >= 3, conditional on integer
coefficient forms, the stated rate bounds, and arbitrarily late nonvanishing.
An arbitrary index map tending to infinity permits even indices or any
unbounded subsequence. The mass-to-content bound is an explicit hypothesis.

`KernelProjectorContent.lean` proves an integral projection onto the kernel
of a primitive row with a chosen Bezout section, its idempotence, the exact
universal divisibility criterion for its image rows, and independence of
content from that section up to a unit.

`PositiveCancellationCost.lean` proves an exact least-mass calculation
showing that row balance alone does not control positive integral cost.
The example is not the zeta family.

`PrimitivePairNormalization.lean` proves nine algebraic theorems, including
nonvanishing and coprimality after dividing each coefficient pair by its
own gcd. For Gram entries A,B,C, the new trace is A/h_a^2+C/h_b^2,
bounded above by (A+C)/Gamma^2. This permits extra selected-vector savings
without imposing the reduced-basis hypotheses after unequal scaling.

## Remaining application

For each fixed higher odd weight one must construct nonzero nonnegative
integral vectors cancelling all lower-period rows, and prove that their
mass divided by the actual image content has an upper exponential rate
strictly below the analytic budget. Subexponential relative cost would
suffice, but has not been established for these constructions.
Alternatively one may use the signed-pair trace rate. Theorem 2.1 now
supplies full augmented rank for every specified consecutive-block profile.
The individual-content substitution weakens the shared-content sufficient
condition; that new rate is still unproved for the actual family.
Optimizing over the full rational coefficient lattice further weakens the
condition to a bound for its second successive minimum. Its exact cost
identity does not prove that bound. No route in the twenty-method
comparison is presented as having completed the all-odd theorem.

The Smith formula and the projector identify the integer content exactly.
Neither identity is a lower asymptotic bound for that content. The
weight-five joint content-to-basis-length estimate is also not proved.

Allowing signed weights is valid and does not require a motivic category.
The signed triangle inequality preserves the absolute weight mass, and a
pair of coefficient forms with nonzero determinant cannot both vanish.
For the target-eliminating cofactor vector, however, its surviving constant
is a nonzero integer divisible by Gamma squared. This proves the necessary
bound Gamma squared <= d_n^s * sqrt(r+1) * cofactor_norm * S_n. The proposed
0.03 weight-five cofactor saving is incompatible with the sharp raw
analytic bound, under the augmented-rank assumptions used for that route.
This restricts the cofactor surrogate and does not rule out the weaker
bound for the actual selected forms or the second successive minimum.

## Rebuild

Lean toolchain: `leanprover/lean4:v4.34.0-rc2`.
Mathlib revision: `85e3a25e006c35636f0e53b0e9296caca2685bc0`.
The complete dependency revisions are recorded in `lake-manifest.json`.

From the Lean project directory, with the pinned toolchain installed:

```sh
lake exe cache get
lake build
lake env lean publication/high-weight-criterion/Verification.lean
lake env lean publication/high-weight-criterion/VerifyPrimitivePair.lean
```

From the manuscript directory:

```sh
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```

No nonstandard TeX macros or downloaded figures are required. The manuscript
uses ordinary article, AMS, Latin Modern, geometry, microtype, and hyperref
packages. No submission to arXiv or a journal has been made.
