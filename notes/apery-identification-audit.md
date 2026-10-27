# Apéry-family identification: the verified theorem chain

The published identifications are relevant. They establish specific geometric
period identities. Applying them to the current all-weight coefficient forms
requires retaining the named integral lattice and real period evaluation.

## The classical Apéry family is identified

[Golyshev–Kerr–Sasaki, Apéry Extensions, Theorem 1.1 and Section 5.4](https://arxiv.org/html/2009.14762v3) construct the higher normal function for
the Landau–Ginzburg mirror of the Mukai threefold V12. Their operator is

\[
L=\theta^3-t(2\theta+1)(17\theta^2+17\theta+5)+t^2(\theta+1)^3.
\]

They compute `v0=2 zeta(3)`, `v1=10 zeta(3)-12`, and `LV=-12t`.
The normalized Apéry constant is `zeta(3)/6`. This identifies the classical
weight-three period; it is not a statement about every odd weight.

The exact expansion of this operator has theta-squared coefficient
`3t(t-17)`. It therefore matches `aperyStandardPFPolynomialOperator` in the
repository. The older separately encoded expression with `2t(t-17)` is a
different operator. The modern source removes that ambiguity for the
classical comparison; the earlier difference identity is retained as an audit.

`AperyModernIdentification.lean` verifies the operator expansion and proves
uniqueness from the recurrence and two initial coefficients. Its period
identification theorem states its recurrence hypotheses explicitly. It does
not import geometric existence as an axiom or assert the unproved recurrence
for every finite harmonic expression already in the repository.

`AperyFormalPeriod.lean` strengthens that step. It defines the Euler operator
on formal power series over any characteristic-zero field, computes every
coefficient of the standard Picard-Fuchs operator, and derives the recurrence
from the inhomogeneous differential equation. From

\[
LA=0,\quad LB=12t,\quad LV=-12t,
\qquad A(0)=1,\ B(0)=0,\ V(0)=2z
\]

it proves the full formal identity `V=2z A-B`. Setting `z=zeta(3)` gives the
formal identification for the published period once its differential
equations and constant terms have been supplied. This step does not prove
the geometric existence of a normal function in each higher weight.

## Extension and geometric-realization theorems

[Kerr, Unipotent extensions and differential equations](https://arxiv.org/html/2008.03618) gives uniqueness of the rational VMHS in
Theorem 9.2 under its stated D-module, filtration, and monodromy conditions.
Theorem 9.7 realizes the `m=1` extension geometrically under the good,
reflexive, tempered hypotheses. Theorem 10.10, additionally assuming degree
two, identifies its normalized normal-function value with an Apéry constant.
These are useful identification theorems; geometric realization at `m=1`
must not be silently replaced by realization for all extension lengths.

## The recent integral refinement

[Kerr, Three vignettes on hypergeometric normal functions, Section 5](https://arxiv.org/html/2602.04128#S5) constructs the Ur-convolution extension
and pulls it back along a Hodge class. For an integral local system it uses
the cone

\[
\mathscr J=\operatorname{Cone}
\{\mathbb H_{\mathbb Z}(p)\oplus\mathscr F\longrightarrow\mathscr C\}
\]

to encode integral normal functions. The residue identity (5.5) explicitly
compares infinitesimal and topological singularities after tensoring with
the rationals. Section 6 also tracks nontrivial integral generator indices.
This supplies an appropriate integral comparison target, rather than a
numerical estimate for our particular coefficient gcds.

For each `N,s`, the missing identification is a framed integral comparison
between our presented module

\[
\operatorname{coker}[U_{N,s},V_{N,s}]=\mathbb Z/g_{N,s}\mathbb Z
\]

and a specified torsion subquotient of the geometric integral complex.
It must also identify the evaluated row with the stated real odd-zeta
linear form. A rational isomorphism alone does not determine this content:
the rows `[1,0]` and `[p^m,0]` become equivalent over the rationals, while
their integral cokernels have different p-power torsion.

The new `IntegralFramedComparison.lean` makes an exact sufficient comparison
condition precise. If an integral lattice equivalence `e` satisfies
`[U,V] e = d [A,B]`, then

\[
\gcd(U,V)=|d|\gcd(A,B).
\]

This is proved for all integer rows, including degenerate ones. It transfers
known content from a constructed source row, with its multiplier retained;
it does not manufacture a content estimate for that source. The same module
constructs the coefficient-cokernel equivalence over every commutative ring
and proves that the primitive row is surjective.

## What the 2026 extensions establish

[Ovcharenko, On Arithmetic Mirror Symmetry for smooth Fano fourfolds,
September 2026 revision, Theorem 1.5 and Corollary 1.7](https://arxiv.org/html/2604.26592v4) proves temperedness and specified
fourfold results. Its listed Apéry constants are zeta(2) and zeta(4), with
the cycle-normal-function correspondence in Corollary 1.7 applying to
the designated cases. It states the broader arithmetic mirror-symmetry
assertion as Conjecture 2.2 and considers constants up to rational multiples.

[Golyshev–Kerr, The arithmetic of Calabi–Yau motives and mobile higher
regulators, Theorems A and B](https://arxiv.org/html/2409.19549v2)
constructs regulator cycles for specified rank-four, weight-three motives
and extends particular cycles to integral models at listed parameters.
Those integral-model statements are not an identification of our Hankel
coefficient complex for all weights and indices.

[Dummigan–Golyshev–de Jeu–Kerr, The 2-part of the Bloch–Kato conjecture,
Theorem 1](https://arxiv.org/html/2605.11100) proves explicit indivisibility
and regulator divisibility bounds for K2 classes on a twisted Legendre
family under stated arithmetic conditions. It distinguishes the integral
model lattice from the regulator-defined lattice. Its bounds concern that
family and the prime two, not all primes in our coefficient gcd.

## The chain normalization actually constructed here

`GcdDecalage.lean` constructs a cochain complex over any commutative ring,
its integer content ideal, the source lattice for decalage, a divided
comparison morphism, and explicit versions over the p-adic integers.
The eligibility statement is exact:

\[
(\eta_{p^k} C_{N,s})^0=C_{N,s}^0
\iff p^k\mid U_{N,s}\text{ and }p^k\mid V_{N,s}
\iff p^k\mid g_{N,s}.
\]

This is the coefficient calculation behind the decalage operation in
[Bhatt–Morrow–Scholze, Integral p-adic Hodge theory, Section 6](https://arxiv.org/abs/1602.03148). The general derived functor and the
geometric comparison results are not formalized in this Lean file.

The exact audit `scripts/coefficient_chain_audit.py` includes all common
factors, including an extra factor `11^2` at weight nine and size five.
The tested normalized forms still have negative smallness budgets.
No theorem above has been used to assert an all-odd irrationality result.
