# Exact entropy threshold scope

The paper derives the exact exponential multiplier-mass rate for
m_n/n->beta by uniform factorial bounds and maximum-term comparison.
It proves that the rate is below log(4) exactly when beta<1/2, equals
log(4) at beta=1/2, and equals log(6sqrt(3)) at beta=1.

Four Lean lemmas check the stationary polynomial, strict concavity,
half-radius polynomial identity and exact logarithmic saddle value.
The full asymptotic, parameter-transfer discussion and application to
the family remain paper arguments. This is not a formalized all-index
bound for the selected partial quotient a_n^*.

saalschutz_entropy_threshold.py gives rational logarithm enclosures
at beta=1/4,1/2,3/4,1 and exact coefficient-mass checks at n=40,80,160.
Its output explicitly marks the selected partial-quotient rate unproved.

The five proposed methods are compared in exact-multiplier-entropy.md.
No claimed pointwise transfer-operator estimate, certified analytic tail,
holonomic recurrence for the selected CF digits, or complete arithmetic
transfer from W to those digits has been proved. No unconditional
irrationality theorem is attached to the new entropy calculation.

The existing manuscript main.tex was edited in place and compiled
successfully with the desktop compiler. No replacement exported PDF
or fresh full-project Lean rebuild is claimed.
