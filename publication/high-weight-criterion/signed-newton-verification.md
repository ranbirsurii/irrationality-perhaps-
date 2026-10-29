# Signed Newton transform scope

Four new Lean theorems in ParametricWeightShift prove the unshifted and
shifted generalized binomial convolution at all natural indices, with
k<=m in the shifted theorem, the backward Pascal step, and its all-order
finite-difference consequence. Ring.choose_neg identifies the negative
upper argument with the alternating binomial factors. No mathematical
axiom or placeholder is introduced.

The paper derives all binomial moments by differentiating the finite
coefficient identity, then uses Newton interpolation to obtain an exact
signed transform for any amplitude values f(0),...,f(m). This finite
Newton theorem and the full Laurent-family identification are paper
arguments, not broader conclusions claimed from the Lean theorems.

signed_newton_transform.py checks 1771 exact moment identities, 693 exact
rational convex identities, and eight
actual Padé-coordinate transformations at weights 7,9,11. Every Laurent
coefficient and the rational term are computed from direct truncated
pole jets and compared with independent logarithmic jets. The expected
even-period cancellations are checked as well. The closed difference
formula and exact rational Cauchy product bounds are checked for all
coordinates in those eight cases.

The actual amplitudes have degree growing with m, but their raw finite
differences are now evaluated exactly. Rising-factorial Vandermonde
proves a positive decomposition with total mass one on t>m, closing the
raw analytic signed bound without the absolute branch-mass multiplier.
The manuscript also proves an all-index Cauchy coefficient bound and
its explicit entropy rate. These are paper proofs; the Cauchy argument
has not been formalized in Lean. No sufficient primitive arithmetic
gain follows from them. The negative normalized cost rate and the
all-odd irrationality endpoint remain unproved.

The module and its verification driver compiled successfully. The driver
records 18 theorem dependency reports, with only propext, Classical.choice
and Quot.sound and no sorryAx.

The existing manuscript was edited in place and compiled successfully
with the desktop compiler. No replacement PDF or fresh full-project
Lean rebuild is claimed.
