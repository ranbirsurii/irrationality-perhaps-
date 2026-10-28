# Growth comparison and shift arithmetic, 27 October 2026

The three added modules compiled with the pinned Lean 4.34.0-rc2 and
matching mathlib, using `relaxedAutoImplicit=false`:

- `OddZeta/HeightGrowthComparison.lean`
- `OddZeta/HarmonicDenominatorGrowth.lean`
- `OddZeta/ThirdIntervalPrimeCost.lean`

The growth module proves power and power-logarithm comparison limits,
squeeze bounds for the shifted denominator, fractional-power lower
envelopes, and logarithmic smallness at the critical exponent. The
numerator growth bounds are explicit hypotheses, not proved estimates
for the actual primitive Hankel coefficients.

The harmonic modules prove that primes `a/2 < p <= a` contribute `p^s`
to the reduced denominator of `H_a^(s)`. They also prove the stronger
version for `a/3 < p <= a` after excluding `p | 2^s+1`, including the
product over all such primes. For an exact identity
`H_a^(s) = p/u + c/m`, the prime-product power divides `u*m`.
The lower bound on `u` is proved whenever an upper bound on positive
`m` is supplied.

The paper centers the actual determinant and proves
`m = D^N A`, `0 < A <= 1`, where
`D = product_(k=1..2N-2) (a+k)^s`. This supplies `m <= D^N`.
The centered determinant calculation, positive Gram bound, Chebyshev
combination, and final large-shift divergence theorem are paper proofs;
they are not represented as fully formalized theorems in these modules.

The exact audit `scripts/shift_growth_audit.py` passed 16 centered
certificates and 28 larger prime-cost certificates. It checks all gcd
reduction through the actual reduced denominator in the centered cases.
The larger cases use only the proved universal lower bound, not a fitted
rate. All comparisons use exact integers and rational numbers.

Reproduce the arithmetic audit with Python 3.11 or newer, standard
library only:

```text
python scripts/shift_growth_audit.py --output shift-growth-audit.json
```

Rebuild the Lean project and foundation reports with the pinned toolchain:

```text
lake exe cache get
lake build
lake env lean scripts/AuditGrowthComparison.lean
```

The 28 foundation reports are saved in `lean-growth-verification.txt`.
They use only the standard Lean foundations `propext`, `Classical.choice`,
and `Quot.sound`, as applicable, with no `sorryAx`. No project axioms,
proof placeholders, percent characters, or hidden formatting characters
were added to the new Lean/TeX sources.

The complete project entry point also compiled after the final additions.
The paper compiled in both the desktop editor and Tectonic. All four final
rendered pages were inspected; the final log has no overfull or underfull
box warnings.

The new four-page article is `height-growth-note.tex`, rendered as
`height-growth-note.pdf`. It proves that shifts with
`N^2 log(a_N+2N) / a_N -> 0` make the normalized primitive height diverge.
It does not prove a sufficient upper bound for smaller shifts or the
irrationality of every odd zeta value. Authorship and submission metadata
remain unset, and the source bundle is a research draft.
