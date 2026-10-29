# Ideal and analytic growing-range bridge

Eleven new universal statements in BinaryGaussCertificate.lean compiled:
determinant pullback, nonzero unimodular images, lower-bound invariance,
quadratic ideal norm identity, scaled determinant, integer value floor,
Schur completion, large-coordinate bound, small-coordinate bound, slope
perturbation, and its uniform range version. The verification driver
records only propext, Classical.choice and Quot.sound dependencies.
Compilation succeeded using a single worker after multiworker checks
stalled. No full-project rebuild is claimed.

The ideal-order interpretation and actual-family growing-range asymptotics
are paper derivations in ideal-schur-growing-range.md and main.tex. The
new Lean statements do not assert an unproved Diophantine lower bound.

The paper chooses a stronger adaptive tail tolerance delta_n=16^(-n).
It derives V_n~zeta(s)(100/99)^(n/2) and a slope perturbation estimate
uniform over every integer in the growing range. Taking minima preserves
the uniform error. The remaining fixed-slope arithmetic minimum is not
evaluated asymptotically; no all-index epsilon bound is claimed.

ideal_schur_rate_bridge.py checks forty previously stored fixed-cutoff
cases by exact rational arithmetic. All norm identities and epsilon
tests pass, with at most two positive slices per case. Those fixed-cutoff
finite data are not samples of a proven all-index adaptive asymptotic
lower bound, and no extrapolation is made.

The existing manuscript was edited in place and compiled successfully
with the desktop editor. No replacement PDF was created. The required
negative normalized common logarithmic rate remains unproved.
