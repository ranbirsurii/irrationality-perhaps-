# Parametric odd weights and the alternative numerator-length construction

The manuscript now uses common parameters s=2r+1, n, B, and i for the
weight, even denominator index, numerator length, and selected primitive
pair. For every fixed odd s>=7, n>=2r, and r<=B<=n, it proves full
augmented rank for the blocks B,B-1,...,B-r. This is an extension of the
existing discrete-residue proof: its degree bound is 2(B-r), while the
boundary, positive zeros, and reflection give 2(B-r)+2 roots.

## Shared formulas and proved bounds

The common block has length B-r. Its combined polynomial is

  Q_(s,n,B,i)(u)=sum_(j=0..r) v_(i,j) ((B-r)!/(B-j)!)^2
                  product_(h=B-r+1..B-j)(u-h(n+h)).

The actual primitive forms are p_i*zeta(s)+q_i, with unimodular integer
coefficient pairs. Their integer lifts have coefficient gcd exactly
equal to their least coordinate denominator. The profile is nonzero.

Multiplication by F_B=(B!/(B-r)!)^2 gives an integer Newton frame. Its
output-to-input content ratio divides F_B. For B=n, the weighted height
J=sum abs(q_ell)(12n^2)^ell satisfies

  norm(v_i)_1 <= J <= 56^r norm(v_i)_1.

For arbitrary B in the stated range the upper factor (14n^2)^r suffices.
Both give the same exponential rate as the normalized vector mass at
each fixed weight. This does not establish a favorable rate.

The normalized raw kernel has the exact weight shift

  T_(s+2,n,m)(t)=T_(s,n,m)(t) (n!/product_(h=0..n)(t+h))^2.

Its phase is explicit for B approximately beta*n. At beta=1 the phase
drops by at least 2log(4) per two-weight step. The elementary moment proof
therefore extends to

  abs(L_(s,n,i)) <= C_s (n+1)^(2s+2) d_n^s J_(s,n,n,i)
                   (2397*4^(s-7))^(-n),
  C_s=12*5^(2s)*3^(2s+(s+1)r).

The raw margin grows by 2log(4)-2 per step. No theorem bounds the change
of primitive J by a polynomial under this weight shift: the lower-period
constraints and the integer coefficient lattice both change.

For every allowed B, the tail beyond n^2 has the proved paper bound

  R <= 2*6^r n^(2r) d_n^s norm(v_i)_1 4^n n^(-(s-4)n).

The known coarse Cramer envelope makes that tail tend to zero faster
than exponentially for every fixed s>=7. Neither this estimate nor the
alternative family proves decay of the finite signed part.

## The three proposed analytic routes

1. Saddle analysis was carried out for the actual raw kernel and its
   shared-parameter phase. It proves the displayed all-weight analytic
   factor. J includes absolute values and a Gauss-reduction choice, so
   the raw factorial saddle is not itself an integral representation
   proving the growth rate of J.
2. A generating series for the even-index heights can be defined, and
   its radius is equivalent to the required growth statement by the
   root test. No independent analytic continuation or radius bound was
   obtained. Such a radius is not assumed from the kernel's G-function
   properties.
3. A limiting companion-matrix estimate would apply to a proved recurrence
   for J or a valid majorant. No such recurrence or majorant with the
   required spectrum was derived. The original coefficient recurrences
   do not automatically govern a nonlinear reduced minimum or primitive
   gcd normalization.

The modern Siegel-lemma and Mellin alternatives remain research options.
[Fischler](https://arxiv.org/pdf/2109.10136) constructs small forms and uses
multiplicity estimates for a whole period system; that result is not a
theorem supplying the isolated target quotient here.
[Brown](https://arxiv.org/html/2604.20741v1) retains an explicit clearing
determinant and transfinite-diameter condition. No identification proving
our required primitive-cost rate is inferred from either framework.

## Verification

`ParametricWeightShift.lean` contains eight new proved theorems for the
actual normalized/poised kernel shift, the phase identity, entropy
derivative and lower bound, the two-weight phase comparison, and the
actual normalized/poised block-length factorization used by the profiles. The
module, `VerifyParametricWeight.lean`, and the root `OddZeta.lean` import
compiled successfully. Their
dependency records in `parametric-weight-axioms.log` use only propext,
Classical.choice, and Quot.sound. No placeholders or added mathematical
axioms are used. The full rank, profile, content, moment, and tail proofs
in the manuscript remain paper arguments.

`scripts/parametric_odd_profiles.py` checks seven original-family cases
at weights 7,9,11,13 and eighteen alternative-length cases at weights
5,7,9,11. It checks the exact inverse images, primitive gcd, integer
frame determinant, content quotient, weighted norm comparison, rational
kernel identity, and weight shift. Its joint moment majorant is checked
against independent Euler--Maclaurin enclosures for all fifty forms.
Among the explicitly tested lengths, B=n minimizes the joint bound in
all five comparison groups. These finite selections are not extrapolated
to an all-index optimality or impossibility theorem. The weight-five
checks do not use or assert the high-weight decay estimate at s=5.

The manuscript compiles in the existing editor. The all-index growth
bound needed to conclude irrationality remains unproved for both
families. No unconditional all-odd irrationality theorem is claimed.

## Combining the constructions without changing the original family

The derivative construction supplies a primitive integer pair (a,b).
For the original full cleared matrix M, set z=(0,...,0,a,b), delta=det M,
and v=adj(M)z/delta. The all-index augmented-rank proof gives delta!=0,
so Mv=z. This transfers the same primitive period expression into the
original blocks, where the earlier analytic estimates apply.

If t is the least coordinate denominator of v, the integer vector tv
has target-and-constant gcd exactly t. Primitive normalization therefore
introduces no additional loss. The analytic bound still contains the
weighted height J(v). The existence of the transition does not bound it.
This full family identification is a paper argument, not one of the
eight newly formalized kernel/phase theorems.

`scripts/check_cross_family_transition.py` verifies eighteen exact
transitions and their integer lifts against the stored independent
primitive-form enclosures. All eighteen transferred majorants exceed
one. These finite checks establish no uniform favorable growth rate.
