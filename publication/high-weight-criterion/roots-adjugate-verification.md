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

This construction exposes the exact cost. It establishes no new negative
cost rate and does not conclude all-odd irrationality. The pure adjugate
columns give the primitive forms zeta(s) and 1, so using them alone cannot
produce decay. A successful mixed-pair selection still needs a proof of
its quantitative bound and nonvanishing.
