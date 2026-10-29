# Adaptive-prefix logarithmic bound: verification scope

The all-index paper construction adapts the finite cutoff while retaining
the kernel and coefficient lattice. An exact rational stopping rule
terminates at every eligible index. The geometric-weight integer basis
gives the complete bound

    0<C_(s,n)<=R_(s,n)<=(9/2)*(4/9)^s<1/64, s>=7.

Thus both unscaled logarithms are less than -log(64). This is not a
strictly negative normalized logarithmic rate. For the adaptive sequence
the proved implication is only limsup log(R_n)/n<=0. Neither convergence
of R_n to zero nor unconditional odd-zeta irrationality is asserted.
No claim is made that an earlier fixed cutoff has the same uniform cap.

MomentMajorant.lean and its driver compile with twenty-seven dependency
records. Eight additions verify the adaptive quadratic bound, a unit
margin, neighboring-form bounds, logarithm negativity, a nonpositive
normalized upper-rate envelope, the stronger seed margin, the uniform
geometric-weight cap, and log R < -log 64. Their dependencies are only
propext, Classical.choice and Quot.sound. There is no sorryAx or added
mathematical axiom. The actual zeta-series interpretation, integral
comparison, profile identification and stopping-rule termination remain
the paper arguments, not extra conclusions claimed from Lean compilation.

adaptive_prefix_uniform_bound.py checks twelve exact rational cases
across weights 7,9,11,13,15,17,21, reaching n=160. Each starts with
K=2n and verifies both stopping inequalities, the signed-prefix bound,
and the uniform cap. All twelve stop without doubling; this observation
is not extrapolated to all indices. The general doubling termination
proof uses fixed-index tail convergence.

The signed-prefix data also retain the rational quadratic-content bound
alpha>=eta and its exact cost upper bound. Its tested values are too
large to establish the desired exponential decay; no asymptotic claim
is inferred from that finite comparison.

The existing main.tex was edited in place and compiled successfully with
the desktop editor. The existing historical exported PDF was not
replaced. No fresh full-project Lean rebuild is claimed; the modified
module and driver were checked directly.
