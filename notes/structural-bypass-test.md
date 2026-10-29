# A bounded test of the four suggested bypasses

No manuscript rewrite is made in this pass. None of the following
frameworks has supplied the complete decay estimate. The existing proved
kernel and moment bounds remain unchanged.

## Selected candidate: compact returns of the normalized moment lattice

Let S_raw be the positive definite binary moment form, with reduced
coefficients alpha,beta,nu, and set d=det(S_raw)>0. Its determinant-one
normalization is Q=S_raw/sqrt(d). Suppose at selected indices its minimum
on nonzero integer vectors is at least c>0. Because the reduced first
coefficient realizes that minimum, alpha>=c*sqrt(d). Reduction gives

    d=alpha*nu-beta^2 >= (3/4)alpha*nu,
    nu <= (4/(3c))*sqrt(d).

Consequently the complete target R=mu*nu satisfies, at those indices,

    R <= (4/(3c))*mu*sqrt(det(S_raw)).

Thus compact returns together with decay of the displayed volume cost
would suffice along an unbounded subsequence. This does not require
uniform compactness or a bound for every shape factor. It does not
assert that either needed property has been proved for this sequence.

The exact finite test uses c=1/100 and checks
alpha^2 >= c^2*(alpha*nu-beta^2), avoiding square roots. Twenty of the
21 stored matrices meet it. The exception is weight 21, index 20. The
script also checks the resulting squared bound for R exactly. It does
not infer an infinite subsequence or a limiting volume cost.

[Kleinbock's quantitative nondivergence notes](https://www.claymath.org/library/proceedings/cmip010c.pdf),
printed pages 131 onward, provide a relevant framework for controlled
families of lattice trajectories. The needed trajectory hypotheses and
estimates for the coefficient functions have not been established here.
An arbitrary indexed lattice sequence is not automatically a geodesic,
a unipotent orbit, or a sequence covered by an equidistribution theorem.
Ergodicity of an ambient action alone does not identify this orbit as
generic. No Ratner or Duke conclusion is invoked for these data.

## Adelic heights

The product formula gives a precise test for the proposed cancellation.
For a nonzero rational vector x, choose a primitive integral vector p
and rational scalar t with x=t*p. Using max norms at all places,

    sum_v log ||x||_v = log max_i |p_i|.

Indeed the scalar contribution is zero by the product formula, and
the primitive vector has p-adic max norm one at every finite prime.
This is the usual projective height calculation; see
[Milne, Elliptic Curves, Heights](https://jmilne.org/math/Books/ectext6.pdf),
printed page 125, Remark 4.12. It keeps the known primitive normalization exact.
An additional benefit would require a proved estimate for the actual
adelic matrix norm or local divisibility, not just re-embedding the
same rational vector. No such estimate was obtained in this pass.

## Tropical valuations

For a determinant, the minimum over permutation sums of entry valuations
is a valid lower bound on its valuation. It is exact if the lowest
valuation contribution is unique; tied contributions require residue
information to determine extra cancellation. This follows directly from
the non-Archimedean triangle inequality and the determinant expansion.
Such lower bounds can certify common divisors without computing a gcd
numerically. No valuation bound strong enough for this family's reduced
moment cost has been derived here. The tropical reformulation is not
used as a substitute for an unproved arithmetic estimate.

## Hodge metrics and quantum modular forms

[Schmid's variation-of-Hodge-structure theorem](https://www.maths.ed.ac.uk/~v1ranick/papers/schmid.pdf)
is a possible source of asymptotic norm estimates after a specific
polarized variation and degeneration parameter have been identified.
No realization identifying the present inverse coefficient metric,
its integral lattice, and its index n with such a variation has been
constructed in this pass. No bound on the second minimum is inferred
solely from the weight of a Hodge structure. Quantum modular or
noncommutative terminology is not introduced without a concrete map.

The modular compact-return route is retained as a research candidate.
The other three proposals produce no proved quantitative improvement
here. This conclusion adds no hypotheses to the manuscript and changes
none of its proved statements. The final product decay remains unproved.
