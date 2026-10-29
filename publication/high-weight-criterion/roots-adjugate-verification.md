# Root and adjugate formulas: scope

The manuscript derives a finite root-partition formula for every Laurent
coefficient of the actual kernel, constructs the full augmented-matrix
adjugate pencil, and evaluates the individual content of each mixed
integer pair exactly. The cofactor roots express its norm as a weighted
distance. Jacobi's complementary-minor identity identifies the root
choices with sparse Cramer vectors and their individual gcds.

The script roots_adjugate_formula.py checks six actual profiles at
weights 7,9,11, 24 image/content/root-mass identities, 53 complementary-
minor identities, and 28 exact primitive root costs. The root-partition
calculation uses the explicit roots and finite integer partitions; its
reference uses harmonic logarithmic jets.

The Lean theorem integer_adjugate_vector_image verifies the full matrix
adjugate image identity. The root-partition expression, coefficient-family
identification, Jacobi specialization and asymptotic implications here
are paper arguments, not claims of full Lean formalization.
The changed module and focused dependency driver both compiled. The
theorem uses only propext, Classical.choice and Quot.sound; its dependency
record is roots-adjugate-axioms.log. The existing manuscript was edited
in place and compiled successfully with the desktop compiler.

## Independent recheck

The expanded check reconstructs the original rational kernel directly
from all Laurent coefficients at 189 rational evaluation points across
weights 3,5,7 and indices 0 through 5, including odd indices and m=0.
This checks the individual pole coefficients, not only their summed
period coordinates.

A separate determinant implementation using the permutation definition
checks 56 invertible integer matrices of sizes two through five. These
include 20 negative determinants and 34 zero target-cofactor entries.
It verifies the adjugate image and content for positive, negative and
zero p or q, 280 complementary-minor signs, and 162 primitive root-cost
identities. The root-mass formula for q=0 is tested separately; for
negative q its prefactor is abs(q). No algebraic correction was needed.

These checks confirm the stated finite identities. They do not prove
the required uniform asymptotic cost estimate, and the formal Lean
theorem still covers the matrix image identity rather than the entire
root construction or irrationality endpoint.

This construction exposes the exact cost. It establishes no new negative
cost rate and does not conclude all-odd irrationality. The pure adjugate
columns give the primitive forms zeta(s) and 1, so using them alone cannot
produce decay. A successful mixed-pair selection still needs a proof of
its quantitative bound and nonvanishing.
