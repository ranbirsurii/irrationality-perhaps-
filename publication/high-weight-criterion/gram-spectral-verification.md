# Gram spectral continuation

The new `OddZeta/GramSpectralBounds.lean` and its dedicated verification
file compile successfully. The seven printed axiom-dependency sets contain
only propext, Classical.choice, and Quot.sound. The module has no added
axioms or proof holes.
The updated integrated `OddZeta.lean` entry point also compiles successfully
with the spectral module exported.

The proofs cover the explicit two-by-two characteristic roots, their sum
and product, the reduced-basis eigenvalue bounds, the condition-number
comparison, the determinant bound using a lower eigenvalue estimate, and
the resulting spectral upper bound for a normalization cost.

For a Gauss-reduced integral kernel basis with Gram entries A,B,C and
H squared = AC-B squared, the unconditional conclusions are

  mu_min >= 1/2,
  mu_max <= 2 H squared,
  C/A <= mu_max/mu_min <= 3 C/A.

The formal statements expose A>=1, A<=C, and 2 abs(B)<=A as the reduced
integral-basis conditions. The code proves these inequalities for the
explicit roots; it does not formalize the entire general Courant-Fischer
theorem or a new motivic realization.

The mathematical application to the actual signed basis forms is detailed
in `notes/normalized-gram-spectral-bound.md`. Under full augmented rank,
at least one of the two integer forms is nonzero and both have the bound

  abs(L) <= sqrt(r+1) d_n^s S_n sqrt(mu_max(G_n)/Gamma_n squared).

A normalized spectral upper rate at most 1/2 would suffice for every fixed
odd weight at least seven, using the previously proved analytic margin.
This is a sufficient hypothesis, not a bound established for the family.
The application and its rate calculation are paper deductions; the new
Lean module proves the linear-algebra inequalities used in them.

As a consistency check on the supplied vectors, the existing weight-five
record at n=1280 satisfies the exact integer inequality

  3 C * 2^640 <= 2 Gamma squared.

Since mu_max<=3C/2, that particular stored record has
mu_max/Gamma squared<=2^(-640). This check uses the existing record and
does not compute new family indices or extrapolate a rate.

Neither rank alone nor the existing operator-level motivic calculations
establish an integral metric comparison controlling the normalized Gram
matrix for every large index. The all-odd irrationality theorem remains
unproved.
