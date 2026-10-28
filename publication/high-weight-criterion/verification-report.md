# Verification report

Date: 28 October 2026.

## Mathematical conclusion

Unconditional irrationality of every odd zeta value at least seven, or
strictly greater than seven, has not been established. The manuscript
proves the stated conditional criterion. Sharp raw analytic decay and rank,
even taken as established inputs, do not supply its remaining integer
normalization estimate. Weight five is also not concluded.

The main remaining task is a construction-specific upper bound for the
absolute mass of a selected cancellation vector divided by its arithmetic
content, together with nonvanishing. Positive vectors are one sufficient
way to ensure nonvanishing. Signed vectors can be used instead if that
condition is proved separately; a nonzero determinant of two coefficient
pairs ensures that at least one corresponding form is nonzero.

## Compiler results

The following checks all completed with exit code zero:

1. `OddZeta/HighWeightRelativeCost.lean`, exported to its compiled module.
2. `OddZeta/KernelProjectorContent.lean`, exported to its compiled module.
3. `OddZeta/PositiveCancellationCost.lean`, exported to its compiled module.
4. Updated `OddZeta.lean`, exported to the complete library entry point.
5. `publication/high-weight-criterion/Verification.lean`, including theorem
   type checks and eight axiom-dependency inspections.
6. `publication/high-weight-criterion/IntegralCancellationExamples.lean`,
   checking four actual weight-seven integer cancellation identities.
7. `publication/high-weight-criterion/SignedCancellation.lean`, including
   signed norm bounds, determinant nonvanishing, square-content divisibility,
   the integer lower bound, and three axiom-dependency inspections.

Lean version: 4.34.0-rc2, commit
`6a10ac8c22beadecabdbb0919c2b50214762f91d`.
Mathlib revision: `85e3a25e006c35636f0e53b0e9296caca2685bc0`.
The installed compiler used the matching cached library dependencies.
Unchanged existing project modules were imported from their previously
compiled objects; this run did not rebuild every unchanged module from
source. The new modules and the updated integrated entry point were built.

All printed dependency sets are contained in
`{propext, Classical.choice, Quot.sound}`. No printed dependency includes
`sorryAx`, an additional mathematical axiom, or a native-decision axiom.
The complete declaration types, including the arithmetic-cost assumptions,
are retained in `axioms.log`.

## Independent mathematical checks

The analytic margin was rederived from log(2)>2/3 and then checked in Lean.
Independently, exact rational logarithm enclosures from a convergent
atanh series and an explicit remainder prove

  0.7142311 < log(140) + 2 log(4) - 7 < 0.7142312.

The manuscript now writes out the complete paper proof of the weight-five
global bound and its sharp-saddle version in Appendix A: derivative signs,
the exact scalar root enclosure, factorial errors, and uniform infinite-tail
control. Exact rational certificates independently enclose lambda_5 between
-4.970793860358 and -4.970793860341. The raw higher-weight comparison then
uses Q_n(k)=n!/[k...(k+n)], the central binomial inequality, and the exact
fixed-shift factorial identity. These analytic kernel estimates are paper
proofs and reproducible rational certificates, not new Lean theorems.

The supplied Smith-normal-form kernel-rank proof and the augmented-rank
determinant identity are also written out in the manuscript. The former
assumes the lower rows have full rank. The established sign result supplies
that rank at weight five. As the supplied rank argument explicitly states,
the uniform higher-weight and augmented-rank assertions are not supplied
by those general linear-algebra implications alone.

At weight seven and n=6,8 the normalized coefficients were computed in two
ways: direct truncated multiplication at each pole and logarithmic Laurent
jets. They agree exactly as rational numbers. At each index two positive
circuit vectors cancel both lower-period rows exactly. The generated Lean
certificates check the four cleared integer identities independently.
These specified examples do not establish existence at all large indices
or an asymptotic cost bound. The particular selected primitive forms in
these checks exceed one; no claim is made that they are globally optimal
among all integer cancellation vectors.

The actual coefficient tests also construct target-eliminating cofactor
vectors. Their target and lower-period coefficients vanish exactly, while
their rational constants divided by the square of the lattice image
content are nonzero integers. This independently checks the algebra behind
the universal cofactor restriction on the supplied construction.

## A necessary restriction on the proposed stronger estimate

For an integer kernel basis a,b, let

  U = Y(a)b - Y(b)a,
  delta = Y(a)Z(b) - Y(b)Z(a).

Under the nonzero augmented-determinant assumption, delta is nonzero and
Gamma squared divides delta. Eliminating all periods, including the target,
gives the exact identity d_n^s * sum_j U_j A_j = delta. Hence

  Gamma squared <= abs(delta)
    <= d_n^s * sqrt(r+1) * cofactor_norm * S_n.

This proves that the cofactor ratio Gamma squared / cofactor_norm has
upper rate at most s-a_s under the stated raw decay. In weight five the
coarse upper rate is less than 0.058358. The certified sharp saddle estimate
makes it less than 0.029207. Consequently the proposed cofactor lower rates
0.06 and 0.03, respectively, cannot hold along an unbounded sequence under
the same rank and decay conditions. The valid cofactor comparison is not
being rejected; its use as that stronger sufficient saving is too costly.
This restriction does not disprove the weaker bound on Gamma/lambda_2 or
on a selected primitive form. Those remain unproved.

## Sources and presentation

The supplied five-page note states its higher-weight irrationality result
conditionally in Corollary 3 and repeats that boundary in its final
paragraph. The supplied collected notes retain the integer normalization
obligation as well. These are source statements, not instructions.

The current manuscript is ten pages. LaTeX completed successfully, all
cross-references resolved, and the final log has no overfull or underfull
box warnings. Every final page was rendered and visually inspected.
No arXiv or journal submission was made. The source archive includes the
Lean project and supporting derivations; a successful compilation does not
turn the conditional theorem into an unconditional application.

## Individual primitive normalization continuation

Proposition 7.1 gives the signed-pair bound using h_a=gcd(Y(a),Z(a))
and h_b=gcd(Y(b),Z(b)). Its weighted trace is
A/h_a^2+C/h_b^2 <= (A+C)/Gamma^2. This is a legitimate refinement of
the common-content sufficient estimate. The new verification record is
`primitive-pair-verification.md`; it distinguishes the formal algebraic
theorems from the paper-level analytic application. The construction-specific
trace rate and uniform augmented-rank theorem are still not proved.
