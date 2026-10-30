# Upper-half prime row congruence verification

The manuscript's included section `upper-half-row-congruence.tex` contains
the uniform paper proof of its two- and five-power rational congruences,
including all harmonic boundary terms. The fifth-power content theorem
excludes the denominator prime 29 and requires n/2<p<=n-3.

The new Lean module `OddZeta/PadicRowTransfer.lean` was compiled successfully.
The driver `scripts/VerifyPadicRowTransfer.lean` reports dependencies for
all five declarations in `padic-row-transfer-axioms.log`. Four use only
propext, Classical.choice and Quot.sound. The fixed coarse row relation
uses no axioms. There are no sorry, admit or custom axiom declarations.

The formal scope is the algebraic passage from scaled row congruences
to divisibility on integer cancellation kernels, with an explicit Bezout
certificate when a unit coefficient is removed. The rational-function
local deformation, harmonic estimates, and prime-density limit have not
been formalized in Lean. A fresh full-project rebuild is not claimed.

The exact Python reconstruction covers 1,380 nonboundary prime-index
pairs through n=240, with four columns each. All 5,520 fifth-order
congruences pass. All second-order scalars equal -153/98 modulo p^2.
Six direct determinantal image-content checks include the sharp
denominator-prime control v_29(Gamma_32)=4.

Additional independent checks, run separately, cover 576 kernels with
all block lengths p<=m<=n for primes 11,13,17,19,23,29 and all even
p<n<2p. Six coefficient reconstructions agree with the independent
partial-fraction implementation. Large-index checks at (480,251),
(480,317), and (500,257) each pass all four column congruences.

The existing manuscript compiles with the built-in editor. No current
standalone PDF export or unconditional irrationality theorem is claimed.
The improved joint divisor lowers the elementary relative-cost exponent
by two; the remaining primitive signed-moment minimum estimate is still
unproved.
