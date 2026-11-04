# Comparing the proposed methods against the actual construction

No finite experiments were run for this comparison. The conclusions below
are mathematical implications and applicability checks, not claims that
all possible versions of each research direction have been exhausted.

The current target is the primitive monic denominator of the powered
Hankel pencil, not the raw size of a Padé sum. The two families must remain
distinguished when transferring results.

| Method | Consequence currently justified | Does it close the rate? |
|---|---|---|
| Large deviations and analytic pressure | A proved LDP could identify a rate; analyticity does not bound its value. The deterministic concentrated example in the chat disproves that proposed inference. | No |
| Motivic weight purity | Requires a specified realization of this pencil and an integral comparison. No such input is supplied by the current construction. | No |
| Spectral triples | No established estimate here for the finite-place denominators of these characteristic coefficients. | No |
| Homological perturbation/local elimination | Unit blocks can be removed exactly using the Schur complement below. | Useful exact simplification; not yet the middle-band bound |
| Newton polygons | Their depth equals the primitive denominator exponent exactly. | Exact invariant, without a proved small growth estimate |
| Newton versus Hodge/Smith comparison | The original-basis negative Smith mass bounds the Newton depth from above. Optimizing the lattice gives equality. | Existing coarse bound remains too expensive |
| Jacobi orthogonality and polynomial arithmetic | Gives the earlier fifth-power upper-half image-content theorem for the linear Padé family. | Not automatically a primitive Hankel denominator theorem |
| Bombieri-Vinogradov | Needs a proved small-modulus residue-class description of the determinant defect. | That description is absent |
| Sextic/cubic mollification | The referenced chat itself leaves the decisive structured mean-value estimate unproved; no identification with this Hankel defect is established. | No |
| Maximum principles and contour bounds | Control analytic sizes once the contour and function are specified. | Do not determine primitive arithmetic content |
| Hypergeometric transformations | Can expose hidden exact divisibility. An identity rewriting the same primitive polynomial does not itself change its value or denominator. | A new relevant divisibility identity is still required |
| Coarse small-prime sieve | The explicit clearing cost below K/M is 37(s+1)/(40M) on the K-squared scale. | Controls this part only |

## The most direct usable combination: Newton depth and local elimination

Let v_G be the Gauss valuation on Q_p(X), defined on a nonzero polynomial
by its minimum coefficient valuation and extended to quotients by
v_G(f/g)=v_G(f)-v_G(g). Its valuation ring is denoted R.

Write a characteristic pencil, after a rational change of basis, as

    H(X) = [ X I + A     B     ]
           [    C      X I + D ].

Suppose A is p-integral. Set U=X I+A. The polynomial det U is monic and
integral, so v_G(det U)=0. The adjugate has integral polynomial entries,
and hence U^(-1) has entries in R. Block elimination gives exactly

    det H = det U * det(X I+D-C U^(-1)B).

If det H is monic, its primitive local denominator exponent is therefore

    D_p(det H) = -v_G det(X I+D-C U^(-1)B).                 (1)

Thus the unit block contributes no denominator depth. No absolute-value
majorant or estimate of its size is required. The off-diagonal correction
must be retained exactly: eliminating it is not free arithmetic cancellation.

This is the determinant version of contracting an invertible block in a
complex. It is a valid way to use the homological-perturbation suggestion
without introducing an unidentified motive or spectral triple.

## What the formula actually says about a clean harmonic block

If B and C are integral and D=-p^(-s)I_r+D0 with D0 integral, then

    X I+D-C U^(-1)B = -p^(-s) I_r+E, with E in M_r(R).

Factor out p^(-s). The remaining determinant is det(-I_r+p^s E),
whose residue is (-1)^r and is nonzero. Consequently (1) gives

    D_p(det H)=s r.                                      (2)

This is an exact algebraic statement, not a numerical experiment.
It shows why merely declaring the remaining harmonic block to be
integral except for its diagonal would not remove the weight penalty.
The improvement must use genuine cancellations involving the correction
matrix, or a better family.

For the actual Lagrange-pole representation, the matrix is

    X I + T^(s) - diag(H_j^(s)),  N<j<=K.

Its polynomial-moment correction T^(s) is not proved integral in the
remaining collision bands. Formula (1) is applicable to any block for
which integrality is established, but a uniform choice leaving a
sufficiently cheap residual block has not yet been proved. In
particular, it is not legitimate to apply (2) by deleting the collision
terms, nor to count a Schur complement identity as a negative-rate bound.

The best justified selection from these methods is therefore the
Newton-polygon invariant together with exact local Schur elimination.
It addresses the actual characteristic polynomial. It has not yet
yielded the quantitative middle-band estimate needed for irrationality.
No unconditional odd-zeta conclusion or new Lean axiom is introduced.
