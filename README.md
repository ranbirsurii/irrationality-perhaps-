# Odd zeta formalization

This project formalizes exact algebraic pieces from both supplied chat texts,
plus the integer-smallness argument needed for an irrationality proof.

## Higher weights and the new supplied notes

The [twenty-method cost comparison](notes/twenty-cost-methods.md) develops
the full rational lattice of integer coefficient pairs as an exact
optimization of primitive cost. Its second Euclidean minimum equals the
best independent-pair primitive cost, with no restriction to a shared gcd
or one chosen integral basis. `PrimitiveCoefficientLattice.lean` verifies
the coefficient-map inverse and the explicit integer lifts and their gcds.
The lattice-geometric optimization is proved on paper. This improvement
does not establish the necessary all-index second-minimum rate; none of
the twenty routes has completed the irrationality proof here.

The [augmented-rank proof](notes/augmented-rank-discrete-residue-proof.md)
now proves, on paper, full augmented rank r+1 and lower-row rank r-1 for
every odd s=2r+1>=5 and even n>=2r in the actual consecutive-block profile.
A zero coefficient combination has an explicit rational antidifference;
its numerator has degree at most 2(n-r), but the boundary and reflection
force 2(n-r)+2 distinct roots. This closes the previous rank obligation.
The note compares ten methods and develops the discrete-residue method.
The Lean root-count companion verifies the corresponding polynomial core;
the full family-specific coefficient identification remains a paper proof.
The primitive arithmetic cost needed for irrationality is still unproved.

The [individual primitive normalization](notes/individual-primitive-pair.md)
replaces the common content by each selected form's own coefficient gcd.
`PrimitivePairNormalization.lean` proves the exact integer division,
primitive-pair nonvanishing, and the weighted Gram and trace bounds without
assuming that unequal scaling preserves Gauss reduction. The manuscript
includes the full derivation. The required asymptotic estimate for that
sharper cost remains unproved; the new rational-antidifference proof
supplies the higher-weight augmented rank.

The [normalized Gram spectral calculation](notes/normalized-gram-spectral-bound.md)
applies the two-dimensional eigenvalue estimates to the actual cancellation
lattice. `GramSpectralBounds.lean` proves the explicit eigenvalue formulas,
Gauss-reduced bounds, condition-number comparison, and the unconditional
gap `mu_min >= 1/2`, with `mu_max <= 2 * H_n^2` for the integral reduced
basis. The note derives the signed-form bound in terms of
`mu_max(G_n) / Gamma_n^2` and states the quantitative normalized spectral
estimate still needed. Rank and the existing operator-level motivic
identifications do not establish that estimate.

The [organized manuscript source](publication/high-weight-criterion/main.tex)
gives an exact Smith-content reduction and a direct comparison extending
the raw weight-five bound to every fixed higher weight. The new
`HighWeightRelativeCost.lean` proves a uniform analytic rate margin greater
than one third for weights at least seven, and irrationality conditional
on eventual bounds for the integral forms and their relative arithmetic
cost. It does not prove that cost bound for the constructed family.

`KernelProjectorContent.lean` proves the exact integral-projection and
divisibility criteria, including independence from the Bezout section.
`PositiveCancellationCost.lean` proves that bounded row balance and
positive integral cancellation can coexist with exponential minimum
positive mass and unit content. That example is not the zeta family;
it identifies why these structural properties alone do not imply the
remaining estimate. Neither all odd zeta values at least seven nor zeta
five have an unconditional irrationality proof in this project.

## Explicit symmetric Padé cancellation

The [Gram and integral-projector derivation](notes/gram-plucker-and-kernel-projector.md)
gives exact min-max comparisons for the cancellation-lattice Gram
matrix and an all-index integer formula for Gamma_n using a Bezout
projector. This incorporates division by g_n before taking the image
content. Locally it reduces that content to four normalized residues.
The Grassmannian calculation adds no independent Plucker equations
in dimension three. These identities do not yet prove the required
content-to-basis-length growth rate.

The [row-balance theorem](notes/row-balance-and-kappa.md) proves
`log(R_n)/n -> 0` for the actual three-block family. A new universal
third-block recurrence certificate has the same limiting operator as
the first two. Poincare-Perron theory and the proved growth cones
give the result, with no finite-index extrapolation. The primitive
normal upper rate improves to less than 5.877168. The actual Gram
discriminant also gives a bound on kappa_n, but its required rate at
most 0.30 is unproved. That rate would suffice conditional on the
still unproved image-content rate; the content obligation is not removed.

The [local-jet and positive-rounding derivation](notes/local-jets-and-positive-rounding.md)
constructs strictly positive integer weights at every even index and
proves an upper bound using the longer reduced-basis length and the
balance of the distinguished row. Adding this candidate removes a
separate search-radius factor from the sufficient cost estimate.
Exact finite-difference and first-lift identities state the outstanding
local minor congruences. Their required higher-order vanishing and the
winning lattice-shape rate remain unproved; earlier finite records
have not been regenerated.

The [quotient-prime loss argument](notes/quotient-prime-loss-and-content.md)
proves that bounded valuation losses supported on divisors of fixed,
nonzero smaller-quotient coefficients total o(n). This handles the
asymptotic size of that particular exceptional set. The local content
bound outside the set and the positive-weight cost remain unproved.
A strictly positive unimodular matrix family also shows why Perron
growth and Mahler measure alone cannot supply a gcd lower bound.

The [analytic large-index extension](notes/analytic-large-index-extension.md)
proves an explicit bound `S_n <= C_0 (n+1)^12 / 140^n` for every even
n>=4, using factorial inequalities, a global saddle bound, and uniform
tail control. It requires no finite-index audits. An explicit exponential
bound holds from n=5,760,000 onward. The primitive integer normalization
cost still has to be bounded before concluding irrationality.

The [three-block enlargement](notes/three-block-positive-forms.md) uses
lengths n,n-1,n-2 and a saturated integer cancellation lattice. The
uniform denominator and positivity theorems apply to this profile.
Exact finite searches through n=1280 produce positive primitive forms
below one; the n=1280 form is below 10^(-126), certified with rational
positive-sum bounds. A new uniform lattice-cost inequality is proved,
but its required limiting rate remains unproved. These finite bounds
do not establish irrationality.
The [uniform block-length recurrence](notes/uniform-block-recurrence.md)
has explicit polynomial coefficients with proved signs. It shows that
the last three blocks generate the whole positive rational cone for
0<=m<=n and states a quantified sufficient arithmetic saving for decay.
That saving is certified at selected finite indices, not proved eventually.
The [prime-divisibility argument](notes/lower-column-prime-divisibility.md)
proves a uniform first-order congruence and an explicit divisor of the
lower-period row gcd. It gives a lower rate above 4.277409 for that gcd
and an upper rate below 6.097870 for the primitive row height. The
stronger image-content prime bound was falsified at n=480, p=47; it is
not used as a theorem. The image-content and lattice-shape estimates
needed for irrationality remain unproved.

The [global sign proof](notes/global-coefficient-sign.md) establishes
`(-1)^(n/2)*alpha_(n,n)>0` and `(-1)^(n/2+1)*alpha_(n,n-1)>0`
for every even n>=2. Two exact third-order recurrence certificates and
a uniform positivity cone prove the result; this is not an extrapolation
from finite sign checks. The two-block weight-five combined form is
therefore nonzero at every such index. The [independent verifier](scripts/verify_sign_recurrences.py)
checks the universal polynomial identities using only integer arithmetic.
`PadeSignRecurrence.lean` verifies the induction, coefficient inequalities,
and positivity of the explicitly defined recurrence states. Their identification
with the actual Laurent-coefficient sequences remains a paper proof.
The winning primitive arithmetic growth bound is still unproved.
The [three-page proof](notes/global-sign-note.pdf) and
[TeX source](notes/global-sign-note.tex) include the recurrence argument
and the precise formalization scope.
The [arithmetic comparison](notes/arithmetic-twists-comparison.md) states
the exact remaining gcd-to-weight inequality and records the scope of
the Connes-Consani twistor and cyclic-homology constructions examined.
The [independent arithmetic audit](notes/primitive-normalization-audit.md)
checks both primitive normalization procedures through index 160. It also
gives exact positive lower bounds exceeding one at the six audited indices
8,12,20,40,80,160. These finite results establish no limiting arithmetic
rate. The new modules and integrated entry point compile successfully;
their dependency report is in the publication folder.
The [determinantal reformulation](notes/determinantal-arithmetic-budget.md)
expresses h_n/M_n as the gcd of two explicit coefficient minors divided
by the lower-period row mass. It also checks why analytic bounds on S_n
do not bound M_n and why modular nonvanishing does not give a gcd lower
bound. The required growth of the determinantal gcd remains unproved.
The [Smith and exterior-square calculation](notes/smith-exterior-square-progress.md)
constructs an exact adjacent-family bridge with a degree-33 common
denominator, extends the recurrence to all three rational period
coordinates, and proves its nonzero Casoratian and compound-matrix
transport. Independent integer-polynomial and unimodular-witness checks
are included. These identify the proposed recurrence lattice; its winning
gcd growth estimate remains unproved.
The [exterior spectrum calculation](notes/exterior-spectrum-and-smith-growth.md)
computes the limiting characteristic polynomial and proves exactly that
the second determinantal divisor of powers of the limiting companion
matrix is `27^(k-1)`. Its arithmetic growth differs from its real exterior
spectral rate. The proposed spectral-to-Smith inference is therefore
false, including in this constant model; no corresponding arithmetic
rate is inferred for the actual varying coefficient lattice.

The [coefficient-sign reduction](notes/coefficient-sign-reduction.md)
constructs exact Cauchy contours and a harmonic-binomial expression for
the weight-five zeta(3) coefficient. `PadeCoefficientSign.lean` proves
the uniform local-amplitude bound `E_(n,m,j) >= (3/2)*H_n^(2) > 0`
for n>0, m<=n and j<=n. The Laurent-coefficient identification is a
paper proof. Its original finite sign evidence is superseded by the
global recurrence argument linked above.

The [proposal refinement](notes/proposal-arithmetic-refinement.md) applies
the new denominator and telescoping proposals to these specific kernels.
The concise derivation is in the [three-page note](notes/pade-arithmetic-note.pdf)
([TeX](notes/pade-arithmetic-note.tex)).
It proves on paper that `d_n^(s-q)` clears every normalized partial-fraction
coefficient at even n and m<=n, and that `d_n^s` clears the rational constant.
An explicit rational telescoper identifies that constant as `G(1)`.
The [exact audit](scripts/pade_arithmetic_budget.py) passes 18,600 coefficient
checks and 19 full-gcd combined-form ledgers, all with one-sign weights.
`PadeArithmeticBudget.lean` proves the leading-magnitude binomial identity,
the block recurrence, positivity for convergent nonnegative combinations,
and invariance of primitive cost under extra common denominator clearing.
The complete denominator theorem is a paper proof. The winning limiting
primitive-cost bound is unproved; a general all-weight one-sign nullvector
theorem is unproved beyond the weight-five result above.

The [symmetric-kernel note](notes/symmetric-pade-note.pdf)
([TeX](notes/symmetric-pade-note.tex)) gives the actual harmonic/polylog
differential equation and a symmetric gamma-ratio kernel with a Barnes
integral. It constructs subsidiary linear conditions that eliminate lower
odd zeta terms. These kernels have their own arithmetic budget; the
single-shift Hankel obstruction is not asserted for them.

`RationalCentering.lean` proves the denominator cost of subtracting a
rational counterterm, including invariance under integer subtraction
and under common rational rescaling of a coefficient pair.
`SymmetricPadePeriods.lean` proves residue-sum cancellation, general finite
period-coordinate elimination, and the explicit rational identities and
actual real-zeta series evaluation giving `112*zeta(5)-107`.
`PoisedKernelPositivity.lean` proves that the actual integer kernel values
vanish at `1,...,m`, are positive thereafter, and force any convergent sum
to be positive. One-sign combinations therefore provide analytic
nonvanishing. The general Barnes contour argument and polylog indicial
calculations are paper proofs.
`PadeNormalizedElimination.lean` proves rational lower-period nullvector
existence and normalization, preserving cancellation and any common bound.
`PadeCombinedFive.lean` proves the actual series identity
`sum_k (601088*S_(2,2,2)(k)+37632*S_(2,2,3)(k)) = 91776*zeta(5)-95165`
and its strict positivity, including the factored rational kernel and
full partial fractions.
The added Lean modules have no proof placeholders or added axioms.

The [symmetric-kernel audit](scripts/symmetric_pade_audit.py) checks 92
weight/index/profile cases across derivative and well-poised families.
The [profile search](scripts/pade_profile_search.py) certifies the best
among 2140 distinct two-kernel forms for zeta(5) at five finite indices.
The first two best primitive forms have absolute value below one; a
sequence tending to zero has not been proved. Exact data and the
[verification record](notes/pade-verification-summary.md) are included.
No full all-odd irrationality claim is made.

The paper also constructs the functional Padé identity for
`1, Li_1, ..., Li_s`, including its high-order zero at zero and subsidiary
conditions at one. Its analytic section proves a saddle-rate limit for
normalized positive sums using exact unimodality and an explicit tail bound.
For weight 5 with block length `m=n`, the rate lies in
`(-4.970794, -4.970793)`. The
[analytic audit](scripts/analytic_sum_control.py) certifies 44 negative
saddle-rate intervals and 22 finite positive-sum bounds. These are estimates
before the final primitive arithmetic cost.
At block length `m=n`, a monotonicity argument in the paper extends analytic
decay to every fixed odd weight: the normalized individual sums are at most
`exp(-1.99*n)` for all sufficiently large even indices. The arithmetic
bound for the final primitive integer forms is still unproved. With block
lengths `m=n-j`, `0<=j<r`, normalizing a nonzero rational nullvector to
sum of absolute weights one cancels all lower periods and preserves
this analytic bound. All-index nonvanishing is still required.

## Growth comparisons and a proved large-shift obstruction

The new four-page [growth note](notes/height-growth-note.pdf)
([TeX](notes/height-growth-note.tex)) applies the proposed polynomial and
logarithmic comparisons and includes the arithmetic cost of changing the shift.
`HeightGrowthComparison.lean` proves the squeeze conclusions with an explicit
numerator bound as a hypothesis. That bound is not established for the actual
primitive coefficient at smaller shifts.

`HarmonicDenominatorGrowth.lean` and `ThirdIntervalPrimeCost.lean` prove the
prime-power divisibility of the reduced harmonic denominator. If
`T_s(a)` is the product of primes `a/3 < p <= a` excluding `p | 2^s+1`,
then `T_s(a)^s` divides that denominator. The modules also prove that an
identity `H_a^(s) = p/u + c/m` forces `T_s(a)^s | u*m`.

Centering the actual Hankel matrix gives this identity with
`0 < m <= D^N`, where `D = product_(k=1..2N-2) (a+k)^s`.
The paper proves the centered determinant bound and combines it with
elementary Chebyshev estimates. For any fixed odd weight, shifts satisfying
`N^2 log(a_N+2N) / a_N -> 0` force the normalized primitive height to
diverge. Thus superquadratic power shifts and exponential shifts do not
prove the desired smallness for this family. No prime number theorem is used.

The [exact audit](scripts/shift_growth_audit.py) verifies 16 centered
identities and 28 larger prime-cost certificates. The three added Lean
modules and their 28 foundation checks are recorded in
[the growth verification record](notes/growth-verification-summary.md).
The all-odd irrationality theorem is still unproved.

## Current arithmetic and Mellin results

The derivational paper is [Arithmetic saturation and toric Mellin models](notes/arithmetic-saturation-note.pdf),
with [TeX source](notes/arithmetic-saturation-note.tex). It is a research draft;
the arithmetic smallness needed to prove every odd zeta irrational remains unproved.

`CofactorArithmetic.lean` proves the exact cofactor expansion, its lower-row
kernel identity, and the full coefficient-content factorization. Writing
the primitive cofactor vector as `c/d`, this gives
`gcd(U,V) = d * gcd(Q sum(c/d), sum(Z[0,j] c[j]/d))` for positive content `d`.
This identifies the remaining arithmetic quantities after the maximal-minor
common factor has been removed.

`MellinRationalMoments.lean` proves the partial fractions, finite remainder
bound, convergence, and zeta evaluation for an explicit all-weight toric
family. For `s >= 2`, put `T = product(x_i)`, `A = product(x_i^i)`,
`B = product(x_i^(s-1-i))`. The series for the period of `A^j B^k/(1-T)`
is rational when `j != k` and is `zeta(s)-H_((s-1)j)^(s)` when `j = k`.
The identity `AB=T^(s-1)` gives an exact finite rational contiguity relation.
The integral interpretation and determinant estimates are proved in the paper.

`PolynomialSmallnessCriterion.lean` proves the integer-polynomial rational
gap and the resulting conditional irrationality criterion. For a polynomial
of degree `m`, the necessary denominator factor is `q^m`.

The four exact audits cover 12 larger primitive Hankel coefficients, 57
balanced/toric determinant polynomials, 32 multiple-Mellin linear forms,
and 12 cofactor certificates. The tested alternative primitive evaluations
all have absolute value greater than one. These finite results do not
establish an asymptotic impossibility theorem. The data, reproducible scripts,
and [verification record](notes/mellin-verification-summary.md) are included.

## Formalized from the chat texts

`OddZeta/AperyStructure.lean` verifies the symmetric-square coefficient
identities for the displayed Apéry root equation, the level-six branch values
`17 ± 12√2`, and the rescaling of the gauge-transformed equation under
`t = 9r`. It also records the three rational coefficients of the displayed
complete third-kind Picard–Fuchs operator.

`OddZeta/AperyFive.lean` defines the finite rational functions `F_n(t)` and
`R_n(t,z)` and proves that their numerator zeros at `1,…,n` persist for every
`z`. It defines the stated Apéry coefficients `A_n`, harmonic numbers,
`eta_(n,k)`, and the explicit formula for `C_n`; proves `A_1 = 5` and
`C_1 = -36`; and verifies the `n=1` forms and the scalar elimination identity
that cancels the `zeta(3)` term. It also gives explicit finite harmonic-sum
formulas for the rational terms `b_n` and `E_n` by computing the local Laurent
coefficients of the rational kernel; these yield `b_1 = 12` and `E_1 = 64`.
The identity for `C_n` is proved again from the second-order Laurent
coefficient. The Adams projector is formalized on a rational vector space and
on the specified weight decomposition: it kills weight 3, fixes weight 5,
and sends a rational weight-0 coordinate to `-7/24` of itself. Thus the
projected period in the formal weight model is `-4 A_n zeta(5) - 7 E_n/24`.
The coefficient `-4 A_n` is proved integral; Lean defines the exact reduced
denominator of `7 E_n/24` and proves that it clears the rational term.

The supplied text states that partial fractions of the infinite series produce
the displayed coefficients. Lean formalizes their finite Laurent/harmonic
algebra, but does not yet prove termwise differentiation and summation of the
infinite series. Likewise, the third-kind operator coefficients are recorded,
but the analytic proof that the integral satisfies the operator is not
formalized here. The weight-space calculation proves the projector once the
specified Adams eigenspace decomposition is given; it does not itself show
that the geometric Apéry family realizes that decomposition.

## Conditional irrationality step

`OddZeta/IrrationalityCriterion.lean` proves that integer-valued multiples
of a nonzero rational linear form cannot converge to zero. It also proves
that explicit bounds `q_n ≤ C exp(beta n)` and
`|L_n| ≤ C' exp(-alpha n)` imply `q_n L_n → 0` when `alpha > beta`.
The manuscript slopes are formalized as
`alpha_n = 4n log(1+sqrt(2))` and `beta_n = 2n+1`; Lean proves their gap is
positive for every `n ≥ 1`.

The manuscript's separate large-`N` construction states the target denominator
rate `kappa_n <= 2n+1` and decay rate
`alpha_n = 4n log(1+sqrt(2))`. The slope gap is now proved, and the generic
Lean theorem turns matching exponential bounds into the required convergence.
The source does not identify its finite-`N` forms with the chat's `R_n(t,z)`
family, so those bounds and nonvanishing still need to be proved for the
concrete deformed and projected forms. The elliptic chat gives the
characteristic formula once the marked point is specified, while leaving the
inhomogeneous regulator calculation as the next step. These statements remain
the status of the chat-derived construction in this project.

## Joint estimate audit

The joint estimate audit is in [ESTIMATE_AUDIT.md](ESTIMATE_AUDIT.md). For the
specific displayed weight-coordinate form `F_n=-4A_n zeta(5)-7E_n/24`, its
weighted harmonic-sum analysis gives

`E_n/A_n -> 4 zeta(5)+8 zeta(2) zeta(3)` and

`F_n/A_n -> -(31 zeta(5)/6+7 zeta(2) zeta(3)/3)`.

Thus this particular projected form has eventual same-sign coefficients and
cannot supply small integer forms, even after arbitrary common-factor
cancellation. `AperyEstimateAudit.lean` checks the consecutive-weight identity,
the weighted local algebra, `A_n>=1`, and the sign/normalization bounds. The
concentration and asymptotic limit proofs are written in the note and are not
yet formalized in Lean.

The note also tests a genuine integer/half-integer sampling replacement, an
explicit kernel whose numerator vanishes on both grids, and its combined
analytic/arithmetic budget. The script `scripts/joint_estimate_audit.py` gives
reproducible exact rational interval checks of four candidate normalizations.
Finite tests are kept separate from the asymptotic claims.

`AperyHankel.lean` supplies a different target-isolation mechanism: determinants
of the moments `zeta(5)-H_(a+k)^(5)` are affine in `zeta(5)`, with rational
coefficients, because the constant part of their matrix has rank one. Lean
proves this determinant identity over arbitrary commutative rings and checks
the rational/real specializations. A positive moment-integral argument in the
audit note gives nonvanishing. Exact finite tests of the primitive integer
forms, including shifts proportional to the matrix size, still give a
negative combined budget. This is a structural alternative to the displayed
projection, with an explicit arithmetic obstacle rather than an assumed
preservation of decay.

## All-weight determinant arithmetic

`OddZeta/OddHankelArithmetic.lean` is a self-contained Mathlib-based file for
every integer weight. It constructs integer coefficients for
`lcm(1,...,a+2N-2)^(sN) det[zeta(s)-H_(a+i+j)^(s)]`, proves the exact
prime valuations and an elementary logarithmic lower bound for that scale,
and verifies division by a certified common divisor. The irrationality
criteria explicitly require decay and arbitrarily late nonvanishing.

The derivational note in `notes/odd-zeta-arithmetic.tex` and its rendered PDF
prove positivity and the fixed-shift determinant asymptotic
`log(Delta)/N^2 -> -log(4)` on paper. They show that the uniform lcm
normalization grows for every integer `s>1`; this does not exclude sufficient
primitive gcd cancellation. The moment integrals and asymptotics are not
formalized in Lean. No unconditional all-odd irrationality theorem is claimed.

`scripts/sparse_hankel_audit.py` performs 700 exact small-space checks and 60
larger sparse/consecutive family checks at weights 3, 5, 7, and 9. Every larger
tested form has primitive absolute value greater than one. These finite
computations do not settle asymptotic smallness for other spaces.

## Integral chain normalization and published identifications

[Exact all-weight endpoint estimates](notes/hankel-christoffel-estimates.md)
give explicit upper and lower bounds for `Delta/A`, using its Christoffel
minimum and a Jacobi-polynomial calculation. For `s=2r+1` and any sequence of
nonnegative shifts, `N^(2r)(N+a_N)^(2r) Delta/A -> (2r-1)!`.
Consequently the primitive form tends to zero exactly when its positive
target coefficient `U/gcd(U,V)` is little-o of this polynomial scale.
This arithmetic height estimate has not been proved.
`OddZeta/HankelEndpointEstimates.lean` verifies the pointwise logarithm and
weight comparisons and ascending-factorial bounds. The variational,
integration, and limiting steps are paper proofs. The exact audit
`scripts/endpoint_error_audit.py` checks 24 parameter choices.

`OddZeta/RowwiseHankelArithmetic.lean` replaces uniform denominator clearing
by the product of the separate row denominators. It constructs the smaller
integer row and proves an explicit common divisor of both old coefficients,
their exact gcd factorization, and the new prime-by-prime and logarithmic
arithmetic costs. The finite coefficient audit records this guaranteed saving
and the remaining gcd separately.

`OddZeta/GcdDecalage.lean` constructs the coefficient cochain complex over
commutative rings and explicitly over the p-adic integers. It proves the
content ideal, the source-lattice condition for decalage, the divided
cochain comparison map, an integral Smith matrix, and prime-power eligibility
for each common-factor division. The general derived functor, pro-etale
comparison theorems, and geometric tropical realization are not formalized.

`OddZeta/IntegralFramedComparison.lean` constructs the quotient equivalence
from the coefficient cokernel to the quotient by its content ideal over any
commutative ring. It proves that the primitive row is surjective. For an
integral source-lattice equivalence `e` and a comparison
`[U,V] e = d [A,B]`, it proves the exact transfer formula
`gcd(U,V) = abs(d) gcd(A,B)`. Thus the lattice multiplier is accounted for.

`OddZeta/AperyModernIdentification.lean` checks the standard operator in
Golyshev-Kerr-Sasaki's V12 calculation and proves the coefficient-identification
step from explicit recurrence and initial-value hypotheses.
`OddZeta/AperyFormalPeriod.lean` defines the actual Euler differential operator
on formal power series, derives the recurrence from its differential equation,
and proves `V = 2 z A - B` from `LA=0`, `LB=12t`, `LV=-12t` and the three
constant terms. These equations are explicit hypotheses; the geometric
period construction and the identification `z=zeta(3)` are not Lean axioms.
[The identification audit](notes/apery-identification-audit.md) records the
relevant 2024-2026 theorem statements and the integral comparison still
required for these particular all-weight coefficient forms.

`scripts/coefficient_chain_audit.py` computes exact common divisors and local
torsion lengths for selected weights and sizes. It includes all common factors,
including an additional factor 11 squared at weight nine and size five.
These finite computations do not establish a sufficient asymptotic saving.

## All-weight Adams projector

`OddZeta/AdamsGeneral.lean` formalizes the projector proposed in the chat texts.
For target weight `2r + 1`, it uses the Lagrange polynomial

`P_r(X) = prod_{1 <= j < r} (X - 2^(2j+1)) / (2^(2r+1) - 2^(2j+1))`.

Lean proves the eigenvalues are strictly increasing, the denominator is
nonzero, the projector kills every lower odd weight, fixes the target weight,
and gives the exact rational coefficient on the weight-zero coordinate. This
coefficient is fixed for each target weight and independent of the Apéry index.

## Hodge-circle and étale weight bookkeeping

`OddZeta/HodgeEtaleWeights.lean` records the realization data for a Tate
graded piece `Q(m)`: Hodge type `(-m,-m)`, weight-cocharacter exponent `-2m`,
étale cyclotomic exponent `m`, and Adams weight `m`. It proves that the Hodge
circle has exponent zero on every Tate twist, so the circle alone cannot
separate the odd-zeta weights. The weight cocharacter does separate them; the
étale and Adams exponents record the same twist index. These are realization
identities, not evidence that the Apéry family maps to such a Tate class.

For each proposed weight `2r+1`, the same file records the Hodge-circle spectrum
`2r, 2r-2, ..., -2r` on the candidate `Sym^(2r) H^1(E)`. It proves the action
is nontrivial for `r ≥ 1`, identifies the zero middle character, and records
the trivial circle character on the residue Tate graded line of the affine
curve `E \\ {O,P}`. This is the associated-graded weight calculation for the
marked affine elliptic curve, not a construction of its regulator class from
`R_n(t,z)`.

## Apéry K3 regulator source calculation

`OddZeta/AperyRegulatorGeometry.lean` records the coefficients of the
inhomogeneous Picard--Fuchs operator for the Apéry K3 normal function and
formalizes a source-side bound for its first forcing coefficient. The central
binomial estimate gives

`binom(2n,n)^2 / (16^n n(2n+2)) ≤ 1/n - 1/(n+1)`.

Consequently the rational partial forcing coefficients are monotone and lie
between 10 and 15; their real sequence converges by monotone bounded
convergence. This checks positivity and convergence for Kerr's K3 forcing
series. It is not a comparison theorem identifying that normal function with
the deformed Apéry kernel or the odd-zeta forms in the chat. No regulator
pairing with `zeta(2r+1)` is obtained from this estimate.

`OddZeta/AperyRegulatorComparison.lean` now gives the operator-level
identification explicitly. It writes the universal `X₁(6)` Weierstrass cubic
and verifies its marked section, normalizes the elliptic Picard--Fuchs
coefficients to the level-six root equation, and computes directly on a
regulator Taylor jet `A + B t` that the coefficient of `t` in the Apéry K3
Picard--Fuchs residual is `B - 5A`. The forcing series bounded above is the
source's expansion for precisely this residual coefficient. Thus the
Picard--Fuchs “identifier” is now an exact operator calculation, with an
explicit elliptic section as input data.

The same file now carries out an explicit algebraic bridge on the elliptic
fiber. If `α, β` are distinct nonzero roots of `x² + A(t)x + t`, it uses
`z = β(x-α)/(x(β-α))`, with inverse `x = α/(1-λz)` and
`λ=(β-α)/β`. Lean verifies the marked section's Legendre coordinate
`ν=(β-1)/(β-α)` and the transformed cubic, including its twist factor. I
also used the chat's explicit one-motive cycle identity `[P]-[O]`: Lean
models this degree-zero cycle, computes its Abel sum as `P`, and checks the
finite-pole coefficients of the algebraic third-kind candidate
`(Y+κ) dx/(2(x-ν)Y)`. Its coefficient is `+1` at `P` and vanishes at the
conjugate point, unlike the bare Legendre-Π differential, whose pole divisor
is symmetric. The cycle computation is an abstract additive-group model; it
does not establish the geometric identification `Pic⁰(E) ≃ E` for this
family. The remaining `-1` residue at `O` follows only after proving the local
expansion at infinity (or invoking and formalizing the global residue theorem);
that step and the relative de Rham/Abel--Jacobi comparison are still open.

The induced-map calculation is now explicit: `cycleAbelSum_inducedMap` proves
that an additive realization homomorphism commutes with Abel summation, and
`markedAbelCycle_inducedMap` sends `[P]-[O]` to the image of `P`. This is the
functoriality law an induced morphism must satisfy. It does not manufacture the
needed correspondence out of the Apéry family. A Mayer--Vietoris/groupoid
construction is a plausible way to assemble local horizontal maps into such a
global correspondence, but it still has to produce those maps and preserve
the marked residue data.

The induced differential-module map is now explicit as well. On the open set
where its denominators do not vanish, the base change is
`x = r(1-9r)/(1-r)`, with formal derivative expressions
`x' = (1-18r+9r²)/(1-r)²` and `x'' = -16/(1-r)³`. Substituting these into
the pullback of the Apéry root equation gives coefficients
`(18r-1)/(r(9r-1))` and
`(10-11r+9r²)/(4(r-1)² r(9r-1))`. The gauge logarithmic derivative is
`h = 1/(2(r-1))`; Lean proves that the transformed coefficients
`P + 2h` and `Q + Ph + h' + h²` are exactly `levelSixGaugeP` and
`levelSixGaugeQ`. Those coefficients are the level-six elliptic root
Picard--Fuchs equation after `t=9r`. Thus the rank-two solution equations
are related by an explicit base-change-and-gauge map; the earlier symmetric
square calculation then gives the standard rank-three Apéry operator.

There is a coefficient discrepancy that must be tracked explicitly. The
standard Apéry Euler operator has `3x(x-17) theta²`, whereas the operator
printed in [Kerr's two-cycles paper](https://www.math.wustl.edu/~matkerr/TwoCycles091712.pdf)
and encoded here has `2x(x-17) theta²`. Lean now proves the exact defect
`L_standard f = L_Kerr f + x(x-17) theta² f`. Thus an inhomogeneous source
must receive that correction when changing between these encoded operators.
The root-equation calculation alone does not identify their normal functions.

This closes the operator-coefficient comparison, not the arithmetic theorem.
The derivative expressions are supplied as rational formulas in Lean and the
coefficient identities are proved algebraically; real-analytic derivative
and square-root branch statements are not formalized. More substantially,
the map has not been lifted to a morphism of the inhomogeneous normal-function
extensions, nor paired with an integral cycle to produce integer linear forms
in `ζ(2r+1)`. The next rigorous step is to construct that extension morphism
and compute its period pairing. Until it yields certified nonzero integer
forms with denominator growth slower than their decay, the conditional
irrationality criterion below cannot be applied.

There is also a direct arithmetic checkpoint. The January 2026, unreviewed
preprint *On the Irrationality of the Odd Zeta Values* claims irrationality
for every odd zeta value. Its parameter selection requires
`g(α) = 1 + q + λα - γ_q(α) < 0`, with `λ=2n+3`. For `λ≥5`, this inequality
cannot hold: if `q+1≤exp(λ)`, convexity and `g'(0)≥0` give `g(α)≥1+q`; if
`q+1>exp(λ)`, the unique minimum is at
`α*=q/(exp(λ)-1)-1`, where
`g(α*) = q(1+log(1-exp(-λ))) + 1-λ+log(q+1) + q log(1+1/q) > 0`.
Thus that version's parameter lemma does not establish the required decay for
the odd-zeta cases. This audit is not a proof that no corrected argument can
work; it prevents us from importing an invalid estimate as a shortcut.

The geometric and arithmetic paths now have clear independent targets. The
geometric target is an actual horizontal correspondence, constructed by local
maps and overlap cocycles. The arithmetic target is an explicit sequence of
integer forms `A_m ζ(2n+1)-B_m` with certified nonvanishing and decay. Neither
target follows from the other, and both are needed for an unconditional
all-odd irrationality proof.

This is still a Picard--Fuchs and fiber-coordinate model. It does not construct
the horizontal correspondence from the chat's deformed kernel to Kerr's K1
cycle, nor identify the normalized third-kind differential and its period with
that cycle's normal function. Those are actual geometric/regulator comparison
claims, not consequences of equality of operator ranks or one Taylor
coefficient.

## Bridge approaches considered

The ten strongest next methods, ranked for the data actually available here,
are as follows. The ranking is a choice of research route, not a theorem that
the methods will prove irrationality.

| Rank | Method | Concrete calculation required |
| --- | --- | --- |
| 1 | All-order deformation and creative telescoping | Construct every `z` coefficient of the actual kernel and its forced extension equation. Implemented below. |
| 2 | Inhomogeneous companion-system map | Extend the homogeneous gauge matrix and match the entire forcing vector. |
| 3 | Formal recurrence and boundary uniqueness | Show a proposed pushforward agrees with the uniquely specified local solution. Implemented for the kernel tower below. |
| 4 | Relative de Rham residue sequence | Construct the class of the marked third-kind differential and its boundary map. |
| 5 | Modular expansion comparison | Match the normalized full expansions of the periods and sources at a cusp. |
| 6 | Kummer or Shioda-Inose correspondence | Give equations for the correspondence and transport the marked cycle. |
| 7 | Picard-Lefschetz thimble pushforward | Transport the actual integration chain and compute its boundary contributions. |
| 8 | Elliptic-polylogarithm residue comparison | Match the class, including the kernel invisible to residues. |
| 9 | Adams action on a constructed extension | Prove that the geometric action induces the proposed eigenspace decomposition and preserves the required estimates. |
| 10 | Integral-lattice comparison | Transport a specified integral class and calculate its denominator after comparison. |

The selected route now has a construction in `OddZeta/AperyDeformation.lean`.
For each nonsingular rational parameter `t`, it constructs the formal Taylor
series of every finite kernel by multiplying explicit inverses of
`(t+j)²+z`. Both the formal kernel and the original rational `R_n(t,z)` satisfy
the same denominator identity, with numerator `aperyNumerator(n,t)²`.
Its coefficient of order zero is proved equal to the original `aperyF`.

Write `r_(n,m)` for the coefficient of `z^m` in that finite kernel and
`G_m(q)=sum_n r_(n,m) q^n`. With
`D_t=(theta+t)²-q(theta+1-t)²`, Lean proves at every order

`D_t G_0 = 1`, and `D_t G_(m+1) = -G_m`.

The induced lifting map is explicit. For any source `s(q)`, its coefficients
are constructed recursively by

`h_0=s_0/t²`,

`h_(n+1)=(s_(n+1)+(t-n-1)² h_n)/(t+n+1)²`.

Lean proves that this gives a rational linear map `H_t`, that
`D_t H_t(s)=s`, that `D_t` is injective on these formal series, and therefore
that `G_(m+1)=H_t(-G_m)` and the entire forced tower is unique. This constructs
the local formal extension at every deformation order. To use it for the
zeta linear forms, the residue or infinite-sum pushforward in `t` still has to
be computed and shown to transport the sources and the arithmetic estimates.

`OddZeta/AperyZetaPushforward.lean` now establishes the first analytic
pushforward for every deformation order. It identifies
`[z^m] R_0(t,z) = (-1)^m/t^(2m+2)`, proves its real derivative formula, proves
summability of the differentiated values at positive integers, and evaluates
their sum as `(2m+2)(-1)^m ζ(2m+3)`. This uses the convergent Dirichlet-series
definition of zeta in mathlib, without an irrationality assumption.

`OddZeta/AperyTelescoper.lean` gives explicit polynomial coefficients
`A(n,z), B(n,z), C(n,z)` and a quadratic certificate `P(n,z,t)` satisfying

`A R_(n+1)(t,z) + B R_n(t,z) + C R_(n-1)(t,z)`

`= P(t+1) R_n(t+1,z) - P(t) R_n(t,z)`.

The polynomial certificate and its application to the actual rational kernel
are both checked in Lean. Its coefficients at `z=0` reduce, after the common
factor `6n^4(n+1)^4`, to the usual Apéry coefficients
`-(n+1)^3`, `(2n+1)(17n²+17n+5)`, and `-n^3`. For nonnegative rational `z`,
the finite sum over `t=1,...,M` is proved to equal the single upper boundary
term `P(M+1) R_n(M+1,z)`; the lower boundary is zero. Passing the differentiated
and coefficient-extracted identity to an infinite sum, and bounding the
projected forms and their denominators, remain necessary for irrationality.

The candidate ways to connect the chat kernel to an Apéry regulator are:

1. Explicitly transform the marked `X₁(6)` section to Legendre coordinates.
2. Find a rational gauge transformation between the two scalar operators.
3. Construct an isomorphism of their first-order companion systems.
4. Compare local exponents and monodromy representations.
5. Match their modular Hauptmodul and theta-series expansions.
6. Build the relative de Rham residue sequence for `E minus {O,P}`.
7. Normalize the third-kind form using the theta/Poincaré biextension.
8. Identify the class with an elliptic-polylogarithm Eisenstein class.
9. Compute its Rankin--Eisenstein regulator pairing.
10. Construct the Apéry K3 higher-Chow cycle and its normal function.
11. Use a Kummer or Shioda--Inose correspondence to compare the K3 and elliptic motives.
12. Compare the classes through the elliptic-fibration Leray spectral sequence.
13. Match Picard--Lefschetz thimbles and vanishing cycles.
14. Compare limiting mixed Hodge structures at a cusp.
15. Prove uniqueness of the inhomogeneous solution from its boundary expansion.
16. Match boundary residues, then separately control the parabolic kernel.
17. Construct an algebraic correspondence and prove it is horizontal.
18. Compare integral lattices through `p`-adic/étale realizations.
19. Use Frobenius congruences and the Dwork unit-root splitting.
20. Apply creative telescoping to the actual `R_n(t,z)` kernel and compare its
    inhomogeneous equation and boundary values.

Approaches 1 and 20 are now implemented as explicit calculation stages.
Approach 1 gives the marked Legendre characteristic and transformed cubic.
For approach 20, `OddZeta/AperyFive.lean` proves the actual kernel recurrence

`R_(n+1)(t,z) = R_n(t,z) (t-n-1)^2 / ((t+n+1)^2+z)`

under its exact nonvanishing conditions. It then proves coefficientwise that
`G_(t,z)(q) = sum_n R_n(t,z) q^n` satisfies

`[((theta+t)^2+z) - q(theta+1-t)^2] G_(t,z) = 1`,

where `theta = q d/dq`; the initial coefficient is exactly
`R_0(t,z)=1/(t^2+z)`. The proof is entirely formal in `PowerSeries`, and a
positive-`t`, nonnegative-`z` theorem discharges the recurrence's denominator
conditions. This is a new exact equation for the chat kernel, not yet Kerr's
Apéry K3 equation: it differentiates in the generating variable `q`, while
the K3 Picard--Fuchs operator differentiates in the geometric base parameter.
The next concrete bridge is to prove that the actual residue/period pushforward
of this equation in `t` (and the deformation coefficient in `z`) yields the
K3 normal-function equation and its boundary data. That pushforward is not
proved here.

The Scholze-style p-adic route is not the needed bridge at this stage.
Perfectoid/pro-étale comparison theorems compare cohomology realizations for
specified p-adic analytic spaces; the diamonds six-functor formalism supplies
étale operations on those spaces. Neither theorem constructs the missing
cycle from `R_n`, identifies its complex regulator period, or forces this
generating-variable equation to become the K3 equation. A p-adic realization
could help after the algebraic cycle and its comparison map have been built.
The current bottleneck is the explicit residue/period pushforward, so the
formalization keeps its effort there rather than adding an unrelated p-adic
placeholder.

## What is still unproved in the chat construction

The two chat texts are the primary specification. The manuscript copy is only
a secondary aid and does not supply the missing bridges below.

The `n=0` infinite differentiated series has its all-order odd-zeta evaluation
proved. For general `n`, termwise deformation extraction, convergence, and
partial-fraction summation remain to be established for the actual `R_n(t,z)`
family. The finite telescoping certificate keeps its upper boundary term
explicit until those limiting steps are justified.

The geometric lift is not constructed. The chats propose a marked divisor on a
level-six elliptic family and a candidate complete third-kind period, but do
not identify the divisor's actual coordinate in that family or prove that the
resulting period is the regulator of the deformed Apéry coefficients. They
explicitly leave the pullback to the inhomogeneous Picard--Fuchs equation and
the regulator comparison as the next calculation. The separately formalized
Apéry K3 normal function supplies an actual regulator object and an explicit
inhomogeneous equation, but no morphism or cycle comparison has been proved
from it to the chat's deformed kernel.

The all-weight projector is proved as linear algebra, but its application to
the proposed zeta forms still needs a constructed class and a proof that the
class decomposes into the stated Adams eigenspaces. No such class or compatible
Adams action is defined in the supplied chats or in the manuscript aid.

Finally, the irrationality criterion is conditional on concrete projected
integer coefficients, arbitrarily-late nonvanishing, and denominator and decay
bounds. Those estimates have not been derived for the chat's projected forms.
Consequently, this repository does not claim a proof that every `zeta(2n+1)`
is irrational.

All Lean source files use ordinary visible code and contain no `sorry` or
`admit`.

