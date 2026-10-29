# Signed-prefix continuation: verification scope

The continuation proves a uniformly sharper signed-prefix quadratic
majorant and an exact logarithmic rate equality. It does not prove that
the common upper logarithmic rate is negative for the actual family.

Compiled modules:

- MomentMajorant: nineteen dependency records, including eleven new
  statements about prefix energy, tail-power budgets, rational pole
  comparisons, a rank-one determinant, uniform tail-rate positivity,
  and the logarithmic sandwich gap tending to zero.
- PrimitivePairNormalization: ten records, including the integer-form
  rational-denominator bound.
- WeightSevenIntegerCertificate: ten records for explicit integer
  cancellation vectors at weight seven and n=8, their exact contents,
  primitive pairs, coefficient determinant, nonvanishing, exact binary
  metric reduction, and the full cleared rational certificate <10^(-38).

All three modules and their verification drivers compiled. The logs
contain only the usual propext, Classical.choice and Quot.sound
dependencies, or no axioms. No sorryAx or added mathematical axiom is
present. The new certificate uses kernel-checked decide and norm_num,
not native_decide. A fresh root-file check was attempted but interrupted
after remaining without output; no successful full-project rebuild is
claimed.

The concrete certificate's matrix is independently checked in Python
using logarithmic Laurent jets and direct rational-series products.
Lean verifies the explicit arithmetic objects; their analytic relation
to zeta and the infinite sums remains a paper argument.

signed_prefix_metric.py verifies forty exact rational cases across
weights 7,9,11 and five cutoff ratios, reaching n=160. It verifies the
Loewner improvement, unimodular basis, determinant identity, 4/3
sandwich, complete form bounds and separately the signed-prefix tail
residuals. Finite enclosures are checked independently of the moment
majorant. The prefix Bezout construction supplies an explicit upper
bound for every valid certificate; its finite values do not close the
asymptotic estimate. No finite values are extrapolated to all indices.

The manuscript was edited in place and compiled successfully with the
desktop editor. Its live preview is current. The historical exported
PDF was not replaced or relabeled. The full source bundle retains the
explicit conditional scope of the irrationality criterion.
