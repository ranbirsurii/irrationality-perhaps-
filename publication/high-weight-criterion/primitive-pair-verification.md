# Individual primitive-pair verification

Date: 28 October 2026.

`OddZeta/PrimitivePairNormalization.lean` compiles with exit code zero.
The first verification checked its eight initial algebraic statements.
After adding the actual gcd specialization, a clean second build checked
all nine final theorems, with no compiler warnings.
`VerifyPrimitivePair.lean` independently imports the compiled module,
checks all nine declaration types, and prints their logical dependencies.
That check also exits zero. Every printed dependency belongs to
{propext, Classical.choice, Quot.sound}; no added mathematical axiom or
proof hole appears. The declaration types and dependency sets are saved
in `primitive-pair-axioms.log`.

The verified statements are:

1. Diagonal-to-largest-eigenvalue and trace bounds for a general real
   positive-semidefinite two-by-two Gram matrix.
2. Preservation of the Gram determinant inequality under individual
   positive scaling of its two vectors.
3. The corresponding scaled spectral and trace inequalities.
4. The scalar trace comparison with the common-content estimate, under
   positive Gamma<=h_a,h_b.
5. Transfer of the two assumed form bounds to the scaled spectral bound.
6. Exact identification of a divided integer-coefficient form with its
   real-valued quotient, under divisibility and a nonzero divisor.
7. Nonvanishing of at least one individually divided form under a nonzero
   integer coefficient determinant.
8. Positivity of both actual pair gcds under that determinant assumption.
9. Nonvanishing after division by those actual gcds, with both resulting
   integer coefficient pairs coprime.

The spectral proof is direct real algebra for the explicit quadratic
roots. It does not assume that unequal scaling preserves Gauss reduction,
or claim a Loewner comparison with the common-content Gram matrix.

Manuscript Proposition 7.1 explains the actual Padé application: given an
integral kernel basis and nonzero augmented determinant, the cleared period
identity and Cauchy-Schwarz give the two input form bounds. The weighted
trace is tau_sharp=norm(a)^2/h_a^2+norm(b)^2/h_b^2. Raw analytic decay
then suffices if its upper logarithmic rate is below 2(a_s-s).
The analytic application and rate comparison are paper deductions; the
Lean module does not construct the family-specific basis or prove that
asymptotic rate. The uniform higher-weight rank and arithmetic estimates
are still unproved. No unconditional all-odd irrationality claim is made.

The updated ten-page manuscript compiles with both the installed LaTeX
engine and the desktop editor's compiler. A second installed-engine pass
resolves all references; its final log has no overfull or underfull boxes
or unresolved references. All ten pages were rendered and inspected in
a contact sheet, with the new proposition and proof checked at full size.
