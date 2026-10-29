# Arbitrary-weight sufficient target verification

The new criterion allows any pair of independent integer cancellation
weights, with their individual target-and-constant gcds. Its sufficient
cost threshold is log(2397)+(s-7)log(4)-s for every fixed odd s>=7.
The uniform allowance 3/4 is strictly below that threshold.

Compiled Lean additions:

- MomentMajorant.smallness_of_allowed_exponential_cost: an abstract
  decay implication, with the explicit rate hypotheses as arguments.
- ParametricWeightShift.sharp_odd_decay_allowance and
  sharp_odd_decay_three_quarters: elementary logarithmic allowances.

The module names above describe files; theorem names are in namespace
OddZeta. Both modules and both verification drivers compiled. The
parametric driver contains ten dependency records; the moment driver
contains eight. Their records list only propext, Classical.choice and
Quot.sound; no sorryAx occurs. This is not a fresh full-project build.

The threshold script uses rational logarithm enclosures at seven weights.
It verifies the displayed thresholds, not a bound on actual lattice costs.
The manuscript main.tex was edited in place and compiled successfully
with the desktop editor's compiler. The existing historical exported PDF
was not replaced and should not be used as the current manuscript.

Actual-family rank and lattice identifications in this application are
paper arguments. The required all-index arithmetic/geometric cost rate
has not been proved, so no unconditional all-odd irrationality theorem
is claimed by these changes.
