# Continued-fraction root compression

The construction selects a primitive independent pair of convergents
of a rational cofactor approximant, using a certified rational error
delta obtained from the signed kernel prefix. Its coefficient pairs
have determinant +1 or -1, so at least one resulting integer form is
nonzero for any real target. The proof uses no irrationality assumption.

The script cf_root_compression.py passes ten actual profiles at weights
7,9,11 and indices 6 through 20, with thirty signed-prefix certificates.
The weight-seven bounds printed in the manuscript are verified with
exact rational thresholds, not floating-point extrapolation. Independent
Euler-Maclaurin enclosures validate every certificate; they are not used
to choose the convergents.

The compressed signed-prefix tolerances are also bounded by
1/(8(Q0+Q1)). The unit determinant then forces at least one interval
to exclude zero. This gives an exact nonvanishing certificate using
only kernel arithmetic, independent of the zeta-enclosure cross-check.

There are also twelve rational-target controls, for which the common
bound remains at least 1/2, and sixteen Pell controls satisfying the
explicit decreasing bound 3/(2Q). These check that the construction
does not silently assume every target is irrational, and that terminal
continued fractions do not introduce an artificial obstruction to decay.

The two new Lean theorems slope_error_transfer and
nonzero_small_form_of_independent_slope_pair verify error transfer and
existence of a nonzero bounded integer form from the independent pair.
The actual rational-kernel and continued-fraction family identification
are paper arguments. A uniform limit E_n->0, or the sufficient uniform
root-accuracy and denominator-window estimates, remains unproved.

The changed module and verification driver compiled successfully. The
driver records twelve theorem dependency reports, including both new
theorems. They use only propext, Classical.choice and Quot.sound, with
no sorryAx. The existing manuscript compiled successfully after the
construction was added in place. No full-library rebuild is claimed.
