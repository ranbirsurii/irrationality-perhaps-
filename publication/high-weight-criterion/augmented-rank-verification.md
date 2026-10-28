# Augmented-rank proof and formal verification scope

Date: 28 October 2026.

## Mathematical result

Theorem 2.1 of the current `main.tex` proves full augmented coefficient
rank r+1 for the actual normalized consecutive blocks m=n-r,...,n, at
every odd weight s=2r+1>=5 and every even n>=2r. It also proves the
lower-period row rank r-1. The proof uses only rational-function algebra
and a polynomial zero count. No arithmetic decay hypothesis, irrationality
assumption, or finite-index extrapolation is used.

The complete derivation and a comparison of ten methods are recorded in
`notes/augmented-rank-discrete-residue-proof.md`. The chosen method is
explicit discrete-residue rational summation. The external literature is
background for that method; the antidifference and its boundary value
are proved directly for these kernels.

## Two checks on the essential identities

First, coefficient comparison checks every pole of G(t+1)-G(t): the
first coefficient is -b_0=c_0, the interior coefficients are
b_(j-1)-b_j=c_j, and the last is b_(n-1)=c_n. Finite interchange of
the prefix and harmonic sums gives G(1)=-Z(F), including the endpoint
j=n whose harmonic difference is zero. Complementary prefix sums give
the reflected coefficients and G(1-n-t)=G(t).

Second, clearing the common denominator yields

  H(t)=t^s P(t+1)-(t+n)^s P(t).

The next-to-leading coefficient is (d-sn) times the leading coefficient
of P. It cannot vanish because d<=sn-1. Equivalently, if the proper
rational function G starts at infinity with a*t^(-ell), ell=sn-d>=1,
its first difference starts with -ell*a*t^(-ell-1), yielding the same
degree bound. This cross-check confirms both the sign and the one-degree
drop. The boundary and reflection then give 2(n-r)+2 distinct regular
zeros, exceeding the bound deg(P)<=2(n-r). Distinct degrees of the
original block numerators finish linear independence.

## Lean checks

`OddZeta/AugmentedRankRootCount.lean` compiles with exit code zero and
no warnings. `VerifyAugmentedRankRoots.lean` independently imports it,
checks all four declarations, and prints their logical dependencies.
That check also exits zero. Every dependency set is contained in
{propext, Classical.choice, Quot.sound}; no proof hole or additional
mathematical axiom is introduced.
The updated integrated `OddZeta.lean` entry point, exporting this module,
also compiles with exit code zero.

The verified statements are injectivity of the two root lists, vanishing
of a polynomial with more listed roots than its degree, the reflected-root
version, and propagation from P(1)=0 along the polynomial difference
identity at the positive integers. The types expose the degree,
reflection, and difference conditions explicitly. Those conditions and
the actual Padé coefficient-to-antidifference construction are derived
in the paper proof, not fully formalized in this Lean module. Therefore
this record does not claim that an actual all-index matrix-determinant
theorem has already been checked in Lean.

## Manuscript handling and remaining scope

The existing open `main.tex` was edited in place. The built-in document
compiler reports success for the saved source. The editor remains open,
and its live PDF preview uses that source. No separate PDF was compiled
for this request. The repository PDF is explicitly labeled as the prior
ten-page snapshot at revision 16a63c3, before this rank proof.

The earlier primitive-pair module and the integrated library entry point
also passed their completed checks. The rank proof makes the signed-pair
nonvanishing argument unconditional for this profile, but it does not
bound the primitive normalization cost. The all-odd irrationality theorem
still requires that quantitative arithmetic estimate.
