# Fifty strategies for the uniform primitive-cost estimate

This is a research comparison for the actual coefficient families. It is
not a list of fifty proved estimates. Each entry specifies the quantitative
statement needed, rather than relying on the name of a theory. The desired
unconditional conclusion is irrationality of every odd zeta value at least
seven, with weight five an additional target. The estimate needed to reach
that conclusion has not been proved in this document.

## The fixed objective

For s=2r+1 and even n>=2r, let the lower-period kernel have basis a,b,
Gram matrix G, coefficient matrix K, and delta=det(K)!=0. The full rational
coefficient lattice is L=F^(-1)Z^2. Put

  S=K adj(G) K^T,
  U^T S U=[[mu,beta],[beta,nu]], U in GL_2(Z),
  0<mu<=nu, 2 abs(beta)<=mu.

Its optimal independent-pair Euclidean normalization cost is

  W_n^2=lambda_2(L)^2=nu/delta^2.

The existing raw estimate has exponent

  a_s=log(140)+(s-5)log(4), a_s>s+1/3 for s>=7.

The exact target is an upper exponential rate for W_n strictly below
a_s-s, or an adequate unbounded subsequence with that strict inequality.
The full majorant still contains D_n=d_n^s and the raw sum. A method
that improves only a change-of-frame denominator must be checked against
the entire invariant D_n W_n.

## A. Direct quadratic-form and lattice methods

| No. | Strategy | Exact target and assessment |
| --- | --- | --- |
| 1 | Exact Gauss reduction of S | Prove a uniform bound on nu/delta^2. This is the chosen direct route; the minimum identification is now checked algebraically in Lean. The growth bound is not. |
| 2 | Dual first minimum | Prove mu/H^2 has lower rate greater than 2(s-a_s), where H^2=det(G). Planar transference makes this equivalent in exponential rate to route 1. |
| 3 | A symbolic unimodular reduction word | Construct U_n explicitly or recursively and prove its reduced inequalities beyond a threshold. No uniform word or invariant set has been constructed. |
| 4 | Integer quadratic content | Lower-bound eta=gcd(S11,2S12,S22), giving W<=2H/sqrt(3 eta). The bound is valid; on the reused records it is weaker than the common-content comparison. |
| 5 | Pairwise coefficient congruences | Combine gcd(S11,S12) and gcd(S12,S22) with the completed-square identity. Their values alone do not control all integer directions; no closing bound was derived. |
| 6 | Reduced discriminant and ideal class | Identify the class of S and bound the least represented positive integer. The determinant specifies a discriminant, not a lower bound for a particular class minimum. |
| 7 | Rational preimage lattice saturation | Optimize over every primitive coefficient pair, not just a fixed source basis. The exact lattice and optimal cost identity are proved on paper, with inverse and gcd algebra in Lean. |
| 8 | Shared-content reduction | Prove lambda_2(Lambda)/Gamma below the analytic budget. It is sufficient but can be substantially larger than the optimum in route 1. |
| 9 | Individual primitive normalization | Bound the trace norm(a)^2/h(a)^2+norm(b)^2/h(b)^2 for a chosen pair. The scalar and spectral implications are in Lean; the family estimate remains unproved. |
| 10 | Direct ellipsoid or covering bound | Bound the second minimum of the coefficient preimage ellipsoid with a controlled cusp parameter. Covolume alone is insufficient; the cusp bound is the missing quantitative input. |

## B. Arithmetic and local-divisibility methods

| No. | Strategy | Exact target and assessment |
| --- | --- | --- |
| 11 | Higher-order local jets | Prove the required selected-minor divisibilities after the lower-row gcd division. First-order collinearity does not establish these higher powers. |
| 12 | Dwork-type projective supercongruence | Identify an integral Frobenius system and show coefficient rows remain projectively proportional to the needed order. The exact system and congruence order are not supplied by a formal weight comparison. |
| 13 | Lucas and Kummer carries | Obtain valuation savings for actual coefficient sums and minors, not just the individual factorial factors. The proved lower-column divisor is useful but not the full image estimate. |
| 14 | Large-prime trace factors | A new proof gives product_(n<p<=(s-2)n/(k-1)) p as a common divisor of every naturally cleared lower row k, at every weight. Its Cramer-cost improvement is explicit but does not close the budget. It is not a bound on Gamma after dividing minors by the lower-row gcd. |
| 15 | Bounded exceptional-prime losses | Combine the proved o(n) loss lemma with a valid local lower bound outside the exceptional set. The exceptional-set estimate is complete; the complementary local assertion is not. |
| 16 | Primitive Smith factors | Analyze the invariant factors of the actual coefficient map on the kernel, retaining its integral frame. A spectral radius is not an invariant-factor lower bound. |
| 17 | HNF transport | Track the exact integral image under consecutive transfer steps. Any denominators and index losses must be included; no uniform favorable trajectory has been proved. |
| 18 | Integral projector congruences | Use I-u*ell to incorporate division by the lower-row gcd before testing residues. The exact divisibility equivalence is formalized; the required residues are not assumed to vanish. |
| 19 | Hypergeometric denominator identities | Find an Andrews-type multisum identity for the selected combinations, then prove its integer divisibility. A denominator theorem for another rational function is not an identification. |
| 20 | Integral cohomological comparison | Construct the particular source lattice, target frame, and finite-prime scale, then bound the scale. An abstract realization or a rank statement does not quantify it. |

## C. Alternative forms and analytic constructions

| No. | Strategy | Exact target and assessment |
| --- | --- | --- |
| 21 | A shift m approximately beta*n | Optimize the raw saddle and the true coefficient denominator together. A discovery scan with the elementary cofactor bound did not produce a closing margin. It does not rule out sharper arithmetic savings. |
| 22 | Fixed-offset profile optimization | Change the consecutive profile while keeping a proved normality theorem and compute its entire primitive cost. Rank alone does not select a low-cost pair. |
| 23 | A block window of width proportional to n | Use many lower-period relations, but obtain two small vectors independent modulo the full coefficient kernel. Small vectors that give identically zero forms do not suffice. |
| 24 | Combine nearby denominator sizes | Use blocks at several n, with a common clearing factor and the actual quotient metric. The denominator of the combined construction must be recomputed. |
| 25 | Multiple Pade parameters | Optimize numerator zeros, denominator poles, and all lower-period constraints simultaneously. No winning isolated-target parameter choice was found in the elementary budget examined. |
| 26 | Hermite-Pade normality plus heights | Strengthen the proved rank result to a quantitative estimate for integer normal forms. The degree zero-count proves normality but supplies no height estimate. |
| 27 | Differentiate a lower-order rational form | The even derivative shifts pole orders, potentially leaving only the target period. The positive-integer zeros generally cease to vanish after differentiation, so the finite boundary terms and their denominators must be controlled. |
| 28 | Positive integral combination | Construct nonnegative integer cancellation weights with a proved cost. Positivity ensures nonvanishing, but it does not make those integer weights small. |
| 29 | Symmetry projector on rational kernels | Produce a concrete lower-period annihilator and prove the norm of its integral action. Rescaling a rational projector without its denominator is not an arithmetic saving. |
| 30 | Hankel or nonlinear polynomial forms | Replace the two-linear-form cost by complete coefficient normalization of a positive determinant polynomial. The existing shift-height obstruction must be avoided by a genuinely different allocation or denominator estimate. |

## D. Recurrence, dynamics, and certified-tail methods

| No. | Strategy | Exact target and assessment |
| --- | --- | --- |
| 31 | An n-recurrence for the reduced coefficients | Derive a valid recurrence for mu,beta,nu or a controlled piecewise system. Reduction is nonlinear; a recurrence for unreduced entries is not automatically one for their minima. |
| 32 | The exact block-length recurrence | Use the already proved recurrence while controlling the induced integral image. Its rational positive-cone relation alone does not bound primitive weights. |
| 33 | Casoratian determinant transport | Track delta and the Gram determinant together, including their scales. Nonvanishing is now available, but separate determinant growth does not control the reduced diagonal nu. |
| 34 | Exterior-power recurrence | Use the exact exterior operator on the selected integral data. A large exterior spectral radius does not by itself control the lattice minimum. |
| 35 | Birkhoff-Trjitzinsky expansions | Derive uniform expansions for the actual metric and its connection coefficients, then account for integer reduction. Formal leading solutions alone leave the arithmetic direction unresolved. |
| 36 | Positive or invariant cones | Prove that the actual normalized recurrence preserves a set forcing the desired reduced inequality. Such a cone has not been established for the reduced cost sequence. |
| 37 | Certified interval tail | Give an all-index polynomial/rational remainder bound and a forward-invariant region after an explicit index. A collection of finite successes is not the tail theorem. |
| 38 | Cumulative polynomial bridge control | Use the degree-33 bridge with every scale and index retained. Its pointwise polynomial denominator has a proved subexponential rate, but iteration and the primitive quotient need their own control. |
| 39 | A controlled integer frame for the recurrence | Conjugate the actual recurrence into a lattice-preserving frame with small norm distortion. A rational conjugacy with an unbounded integral index does not achieve this. |
| 40 | Periodic or Floquet renormalization | Exhibit a proved periodic reduction scheme for the actual transfer matrices. No such periodic scheme is inferred from a limiting real companion matrix. |

## E. Global Diophantine and geometric methods

| No. | Strategy | Exact target and assessment |
| --- | --- | --- |
| 41 | Quotient Siegel lemma | Find short vectors whose images are independent modulo the full coefficient kernel. Standard short relations may all give zero period forms when the block family is enlarged. |
| 42 | A nonzero linear-form lower bound | Prove a lower bound for every nonzero integer combination of the two projected rows. A theorem that assumes the target is irrational cannot be used to establish it. |
| 43 | G-function value estimates | Verify the actual evaluation point, differential system, height constants, and specialization conditions. General small-argument theorems do not automatically apply at a polylogarithm boundary point. |
| 44 | Logarithmic-form methods | Construct an actual expression in logarithms of algebraic numbers to which a lower-bound theorem applies. Such an expression for the target is not assumed. |
| 45 | Modular or automorphic identification | Identify the concrete coefficient lattice and integral Fourier data, then derive its metric estimate. Equality of weights or period dimensions is not that identification. |
| 46 | Arakelov slopes or height comparison | Prove a bound for this integral frame's distortion. A change of metric must also preserve or bound the raw period functional. |
| 47 | Quantitative nondivergence | Prove that the deterministic sequence of actual coefficient lattices avoids the cusp at the required rate. An almost-everywhere statement does not identify this sequence. |
| 48 | Continued-fraction return estimates | Bound the relevant reduction quotients uniformly or on a sufficient subsequence. Finite continued-fraction prefixes cannot exclude a rational limit with a larger hidden denominator. |
| 49 | CM/Hecke interpretation of the binary forms | Identify the particular isogeny classes and prove a pointwise minimum bound or an admissible choice theorem. Equidistribution of a full family is not a bound on a specified member. |
| 50 | Cancellation in the final integral rather than its norm majorant | Construct the final integer combination explicitly and prove its nonzero saddle contribution, with all coefficient normalization included. This may avoid an overstrong norm criterion, but no such full combination estimate was obtained. |

## Selected tracks and results of this pass

The most direct track is 1-3: the dual integral binary form gives the exact
optimum, with substantial room in the previously computed examples. The
new Lean modules `BinaryGaussMinimum.lean` and `DualCoefficientGram.lean`
verify the first and independent-pair minimum statements, the sharp
squared transference comparison, the determinant and adjugate identities,
and positivity for the actual algebraic Gram formulas. They do not assert
a uniform growth estimate for the family's reduced minimum.

Track 21 was examined by varying the numerator length and counting both
the denominator and a generic cofactor construction. The elementary bound
for the lower-period coefficient rows grows quadratically with the weight,
whereas the raw analytic improvement does not compensate for it. The
numerical scan was only a discovery calculation; it is not a no-go theorem
for another choice of forms or better arithmetic savings.

Tracks 23 and 41 were examined together. Enlarging the block family adds
many inexpensive relations, but the full formal coefficient map still has
fixed rank. A short-vector theorem can populate its kernel with identically
zero forms. It must control the two-dimensional quotient to establish the
needed nonzero pair. The quotient condition cannot be omitted.

Tracks 11-15 remain a genuine alternative. The local first-order formula,
the proved lower-column divisor, and the exceptional-prime loss lemma do
not yet establish the required higher-order normalized minor valuations.
Their precise higher-order statements remain the target, rather than a
consequence of an interpolation or Frobenius label.

Track 14 now supplies an additional proved result for the actual family.
The finite-field translation trace lowers polynomial degree by p-1 and
forces the lower coefficient sums to vanish modulo primes in explicit
intervals above n. Dividing the naturally cleared rows by these common
prime products improves the all-index Cramer envelope. The exponent saved
is ((s-2)/2)H_(r-1)-(r-1), exactly 7/4 at weight seven. The remaining
envelope still exceeds the analytic budget. The full proof and comparison
are in `uniform-coefficient-and-prime-envelope.md` and the manuscript.
Five Cramer-envelope and six finite-field trace theorems also check in Lean.
Seven independent exact cases check all block lengths, 226 coefficient
bounds, 506 prime divisibilities, and 70 full trace-polynomial identities;
these support the implementation and are not the all-index proof.
A central-binomial product majorant saves a further
(r-1)log(32/27) in the envelope's exponent. It too is proved at every
eligible index and checked independently; the refined exponent still
does not meet the required rate.

## Literature scoped to the actual task

[Fischler-Rivoal, On the values of G-functions](https://rivoal.perso.math.cnrs.fr/articles/gvalues.pdf)
provides a general framework for rational G-approximations; its discussion
of irrationality explicitly retains the competition between convergence
and denominator growth. The existence of a G-function representation is
not the arithmetic cost bound needed here.

[Fischler-Rivoal, Rational approximation to values of G-functions](https://www.imo.universite-paris-saclay.fr/~stephane.fischler/approxG.pdf)
imposes an explicit small-rational-argument condition whose constants
depend on the function. An evaluation at 1, or an unquantified analytic
continuation to a different representation, is not an automatic application.

[Brown, Mellin transforms, transfinite diameter and rational approximations
of integrals (2026)](https://arxiv.org/html/2604.20741v1), Sections 7-8,
provides a genuine alternative via a full Mellin matrix and its clearing
determinant. Its linear-form criterion retains that determinant and a
transfinite-diameter bound. With more than two periods the stated conclusion
is that their rational span has dimension at least two; this does not isolate
a prescribed odd zeta value. Applying it here still requires a two-period
construction with its full denominator estimate, or a stronger quantitative
elimination theorem. Neither is inferred from positivity or cohomological
rank alone. This route did not yield a closing estimate in this pass.

[Fischler, Linear independence of odd zeta values using Siegel's
lemma](https://arxiv.org/pdf/2109.10136), revised November 2025, constructs
small forms and a quantitative multiplicity argument to improve a lower
bound on the dimension of a span. Its extrapolation supplies many
independent forms in the whole period system, rather than two short
images in the isolated target quotient. No assertion of irrationality
for each individual target is imported from that theorem.

The other relevant checked sources and their applicable scopes are listed
in `twenty-cost-methods.md`; the duality calculation and exact implementation
are in `dual-transference-and-new-proposals.md`. No unverified recent
irrationality claim is used as an input.

## Status

The asserted uniform estimate for nu_n/delta_n^2 has not been proved by
these investigations. Therefore the all-odd irrationality endpoint is not
written as an unconditional theorem. The completed algebraic and analytic
pieces are retained with their exact scopes, not promoted to the missing
arithmetic assertion.
