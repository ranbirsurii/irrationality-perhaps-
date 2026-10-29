# Explicit contour evaluation and logarithmic closure

The supplied master-proof attachment is treated as a proposed argument.
Its statements about computed phases, contours, valuation ceilings, and
negative rates are not imported as mathematical premises.

## Results added

The current manuscript contains a concrete cotangent/gamma contour for
the finite moments of the actual kernel. The positively oriented
rectangle has real sides m+1/2 and K+1/2 and imaginary sides +/-1.
Its residues are exactly the finite summands m+1,...,K. The certified
diagonal tail contributes explicit mixed and tail determinant terms.
The full raw determinant is their sum with the positive double residue
sum. No unspecified contour or omitted pole contribution is used.

The kernel critical equation is

  x^(s+1)(x+2)=(x-1)(x+1)^(s+1).

The paper proves a unique real critical point with strictly negative
second derivative for every s>=7. This is the kernel phase calculation,
not a theorem about the growth of the inverse coefficient profiles.

The finite double-contour prefactor contains

  [P_n(z)Q_n(t)-Q_n(z)P_n(t)]^2.

It vanishes on the diagonal. Its coefficients depend on n, so the
proposed fixed-prefactor Gaussian expression cannot be substituted
without evaluating those coefficients and the relevant derivatives.
An ordinary nondegenerate two-real-dimensional Gaussian contributes
a factor proportional to n^(-1), before additional vanishing factors,
not the one-dimensional n^(-1/2) factor written in the proposal.

The exact logarithmic decomposition and the implication from an eventual
negative logarithmic bound to sandwich decay are proved in Lean.
The manuscript includes an all-odd irrationality corollary with the
actual negative-rate statement explicitly conditional at every weight.
That statement has not been proved for the family. No unconditional
all-odd irrationality theorem is added.

## Formal scope

`MomentMajorant.lean` now contains seven proved statements:

- Exact common-factor cost invariance.
- The homogeneous reduced quadratic upper bound.
- Shifted real-polynomial times exponential convergence.
- The eventual-majorant-to-limit implication.
- The finite weighted Gram determinant double-sum identity.
- The positive scalar logarithmic decomposition.
- The logarithmic-bound-to-sandwich-limit implication.

The module and `VerifyMomentMajorant.lean` compiled successfully.
The full root import check was stopped before completion without a
diagnostic in this run; no fresh full-library build is claimed.
The seven dependency records use only propext, Classical.choice and
Quot.sound. No placeholders or added mathematical axioms occur.
The contour identification, kernel-saddle theorem, actual-family
identifications and negative scalar rate are not claimed to be
fully formalized by these generic lemmas.

`scripts/explicit_contour_determinant.py` evaluates the finite double
residue sum, mixed tail sum and pure tail determinant in exact rational
arithmetic for eight cases at weights 7,9,11,13. It compares their sum
with the independently assembled two-by-two raw determinant. It also
checks rational brackets of the kernel saddle and negative second
derivative on those brackets, and the actual scalar sandwich cost.
All checks pass; none is extrapolated to a limiting coefficient rate.

The existing manuscript compiles successfully in its current editor.
The current source and complete Lean sources are packaged for review.
Any included historical PDF is explicitly labelled as a prior snapshot;
it is not the rendering of the current manuscript.
