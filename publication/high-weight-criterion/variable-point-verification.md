# Moving-point certificate scope

The integer coefficient points are adjacent exact continued-fraction
convergents of the actual rational slope B_n/A_n. The selection retains
the best envelope before or at the first crossing of the balance scale.
Terminal rational and initial denominator-zero points are included.
Their determinant is +-1 and their complete quadratic values are checked.

Two additions to BinaryGaussCertificate.lean prove the variable-point
Schur bound and the exact balance identity. Their hypotheses remain
visible in the theorem statements. The existing independent-pair minimum
theorem gives the minimization step. The driver checks ordinary axiom
dependencies; no sorryAx or added mathematical axiom is used.

The exact script checks forty fixed-cutoff metrics. Every complete bound
is at most 2073/1000 times its Gauss optimum, checked as a rational
inequality. These are not samples of a proved all-index balance theorem.

For the stronger adaptive tolerance 16^(-n), the paper proves
R_n<=20*4^(-n)*(lambda_n^2+lambda_n^(-2)), where lambda_n is the ratio
of the selected denominator to the balance scale. The required upper
logarithmic rate below log(4) for this distortion remains unproved.
The all-odd irrationality theorem has not been closed.

The existing manuscript source was edited in place and compiled
successfully with the desktop compiler. The analytic family identification
and continued-fraction construction are paper arguments. No fresh full
Lean project rebuild or replacement exported PDF is claimed.
