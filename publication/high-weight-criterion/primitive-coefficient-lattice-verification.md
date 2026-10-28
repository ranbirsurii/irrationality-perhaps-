# Primitive coefficient lattice: verification and limits

Date: 28 October 2026.

## Work completed

`notes/twenty-cost-methods.md` compares twenty specific approaches to the
actual cost, including the required construction-specific inputs and the
literature checked. No route is labeled as having proved the missing
asymptotic estimate. The selected exact reduction optimizes over the full
rational preimage lattice of integer target-and-constant coefficient pairs.

For an integral kernel basis a,b and B=(F(a)|F(b)), the rank theorem gives
delta=det(B)!=0. The full coefficient lattice has coordinate description
B^(-1)Z^2, index abs(delta) over the original kernel lattice, and covolume
H/abs(delta). Primitive-normalized integer kernel vectors are exactly
the vectors in this rational lattice with primitive coefficient image.
Its second Euclidean minimum is the attained optimum of the maximum
primitive Euclidean cost over two independent vectors. This is a complete
paper reduction, with all denominator clearing accounted for.

The new manuscript proposition derives these statements, the corresponding
signed-pair upper bound, and the remaining quantitative inequality. It
explicitly says that this inequality is not proved for the Padé family.

## Lean verification

`OddZeta/PrimitiveCoefficientLattice.lean` compiles with exit code zero
and no warnings. `VerifyPrimitiveCoefficientLattice.lean` independently
imports it, checks all eight declarations, and prints their logical
dependencies; it also exits zero. The final declaration types and
dependencies are in `primitive-coefficient-lattice-axioms.log`.
Every printed dependency belongs to {propext, Classical.choice, Quot.sound}.
No added mathematical axiom, proof hole, or native-decision axiom occurs.
The updated complete `OddZeta.lean` entry point also compiles with exit
code zero after exporting the new module.

The checked statements are:

1. Right inverse of the explicit two-by-two rational coefficient map.
2. Left inverse of the same map.
3. Equivalence between integral coefficient image and an inverse image
   of an integer pair.
4. The integer adjugate lifting identity.
5. The square-scaled lifting identity, which avoids a determinant-sign choice.
6. Exact gcd of a square-scaled primitive integer pair.
7. Exact normalization of the square-scaled lift.
8. Membership in the integral-image set after division by a common
   coefficient divisor.

The abstract lattice index, planar Gauss reduction, and second-minimum
optimality argument are paper proofs. They are not represented as Lean
theorems by the eight elementary identities. The family-specific
asymptotic estimate is neither a paper theorem nor a Lean theorem here.

## Required estimate

With L_n the full rational coefficient lattice, an adequate estimate is

  limsup log(lambda_2(L_n))/n < a_s-s,
  a_s=log(140)+(s-5)log(4).

The raw decay and denominator estimates then imply small nonzero integer
forms. The comparison of twenty methods did not establish this growth
bound. In particular a small covolume, determinant nonvanishing, or a
smaller common denominator alone does not supply the second-minimum rate.
No unconditional irrationality result for all odd weights is claimed.

The current open TeX source was edited in place and compiled successfully
with the built-in document compiler. No replacement document or separate
PDF was created. The repository PDF remains the explicitly labeled
earlier snapshot; the live editor preview uses the current source.
