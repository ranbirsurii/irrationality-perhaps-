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

## Working backwards: relative perturbation and cancellation

The comparison must be relative, because separate denominator upper
bounds cannot be subtracted. Write H_s=XI+M_s for the monic pencils and

    E=H_5^(-1)(M_s-M_5).

Then, exactly in Q_p(X),

    P_s/P_5=det(I+E),
    D_p(P_s)-D_p(P_5)=-v_G det(I+E).                       (3)

This is also valid after eliminating unit blocks with Gauss-unit
determinants. It gives a backwards target in the actual relative pencil.

If E=N+R with N nilpotent, one can remove N at zero determinant cost:

    det(I+E)=det(I+(I+N)^(-1)R).

Here (I+N)^(-1) is a finite geometric series and det(I+N)=1, regardless
of how large the denominators in N are. This is a genuine cancellation
mechanism, stronger than bounding the sizes of all entries.

Set W=(I+N)^(-1)R. If rank(W)<=r and every entry has Gauss valuation
at least -a, where a>=0, then

    -v_G det(I+E)<=r*a.                                  (4)

Proof: expand det(I+W) into principal minors. Minors larger than r
vanish exactly; every remaining q-minor has valuation at least -q*a,
and hence at least -r*a. This proves (4) by the nonarchimedean triangle
inequality. Formula (4) would close the required rate if the actual
Hankel relative perturbation admitted such a decomposition with a
sufficiently small prime-weighted sum of r*a. It is not legitimate to
assign that decomposition from the desired conclusion.

## First attempted construction: derive low rank from weight raising

The exact identity 30 mu_7(t^e)=(2e+6)(2e+7) mu_5(t^e) is quadratic
in e. That does not make the matrix perturbation rank two.
For the polynomial-moment Hankel block H=(m_(i+j)), put D=diag(0,...,h-1).
The corresponding transformed block is exactly

    H_new = (4D^2 H+8D H D+4H D^2+26D H+26H D+42H)/30.

Multiplication by D has full growing rank. The displayed formula does
not produce a low-rank or nilpotent relative perturbation. Moreover,
the full rational Hankel pencil contains pole moments; the identity
above is asserted only for the polynomial-moment block.

There is an all-dimension algebraic check of the rank issue. Let
m_e=1/(e+1), the moments of Lebesgue measure on [0,1], and let H be the
resulting h-by-h Hilbert matrix. Applying the same quadratic multiplier
gives

    (H_new-H)_(i,j)=(4(i+j)+22)/30 - 1/(3(i+j+1)).

The first matrix on the right has rank at most two; H is positive
definite and has rank h. Hence rank(H_new-H)>=h-2. Thus the exact form
of the multiplier does not imply a bounded-rank difference, even for
a positive original moment functional. This is a symbolic family,
not a finite experiment or a counterexample to the actual Padé theorem.

## Second attempted construction: use the derivative as a nilpotent

Differentiation on a bounded-degree polynomial space is nilpotent, but
the weight-raising operation above is a polynomial in the Euler operator
t*d/dt, whose monomial eigenvalues are e. It is not a nilpotent
operation. Replacing it by differentiation would change the moment
functional and would require separate boundary and pole identities.
The nilpotent cancellation in (3)-(4) therefore cannot be invoked from
the moment-raising identity alone.

## Other attempts and the stopping point of the deduction

The proposed Newton-polygon method measures (3) exactly, but still needs
an independently established bound. The local lattice construction
in the companion note attains that exact value, but constructing it
from the unknown slopes does not estimate the value. The coarse sieve
controls very small primes only. The character and thermodynamic
arguments need their missing arithmetic identifications or numerical
variational bound; they have not supplied it for this pencil.

Consequently the relative Schur perturbation is the most direct
remaining route among these algebraic attempts, but no proved small
defect decomposition has been obtained for the actual growing Hankel
pencils. This note records failed implications as well as valid
identities. It does not claim that every possible variant of the named
research programs is exhausted, or that iteration must produce the
unconditional theorem.
