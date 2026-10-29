# A direct modular-invariance attempt for the exact moment metric

This pass identifies the modular point of the actual rational reduced
moment form and derives an unconditional scalar comparison. It does not
prove the final limit. No manuscript claims are changed.

Let S_raw have reduced coefficients alpha,beta,nu, with alpha>0,
alpha<=nu and 2|beta|<=alpha. Put d=alpha*nu-beta^2>0 and

    tau=(-beta+i*sqrt(d))/alpha = X+iY.

Then |X|<=1/2, |tau|^2=nu/alpha>=1, and Y^2>=3/4, so tau belongs to
the closure of the standard modular fundamental domain. Since the
coefficients are rational, clearing the polynomial
alpha*tau^2+2beta*tau+nu=0 and removing its full content yields a
primitive integral imaginary-quadratic equation. Thus these are genuine
CM points. This is not an assumed period-map identification.

Changing an integral basis changes the representing point by the
modular action (up to the orientation convention); it does not choose
a different ideal class or a different CM point in a Galois packet.

## Exact weighted cusp comparison

Let V=mu*sqrt(d) and R=mu*nu, the existing complete bound. Direct
substitution gives

    R=V*(Y+X^2/Y),
    VY <= R <= (4/3)VY,
    VY=mu*d/alpha.

The upper bound uses X^2<=1/4<=Y^2/3. It follows unconditionally that

    R_n -> 0  if and only if  mu_n*d_n/alpha_n -> 0.

Here d_n denotes the determinant of the raw moment form, not the lcm
notation used in earlier sections. This criterion allows unbounded Y.
It requires no compactness or nondivergence theorem. It is an exact
scalar formulation of the same remaining target, not a proof of it.

## Quantitative modular-function input

[Bilu--Luca--Pizarro-Madariaga, Rational Products of Singular Moduli](https://arxiv.org/pdf/1410.1806),
Proposition 2.1, gives ||j(tau)|-exp(2*pi*Y)|<=2079 on this domain.
Consequently

    R <= (2/(3*pi))*V*log(|j(tau)|+2079).

This is a valid bound for our actual CM points. The constants are not
fitted to finite data. No adequate height estimate for these particular
singular moduli has been established here. Modular invariance alone
does not supply one.

## Recent theorem applicability

[Ross--Xue, Equidistribution of CM points and RM curves (2026)](https://arxiv.org/html/2605.28614v1),
Theorem 1.1, treats the collection of CM points on a fixed rational
geodesic up to a discriminant bound. Its Theorem 1.4 treats angular
distribution of CM packets of fundamental discriminant in a fixed ball.
Neither statement gives an individual height bound for the one CM point
selected at each index by our recurrence and reduction. We have not
identified our sequence with the required collections or transfers.

[Lindenstrauss--Mohammadi--Wang--Yang (2025)](https://arxiv.org/html/2503.21064v1),
Theorems 1.1 and 1.2, concern effective distributions of specified
translated horospherical or unipotent averages, with an alternative
involving nearby closed orbits. No representation of our discrete
moment sequence as such an average, or exclusion of that alternative,
has been established. These theorems are not invoked as an unconditional
bound on R_n.

Thus modular theory gives a rigorous identification and explicit cusp
estimate, but the final weighted cusp-cost limit remains unproved.
This is a failure to close the estimate in this pass, not a proof that
this family cannot work.

## Checks

`modular_cusp_cost.py` constructs primitive integral CM equations for
all 21 stored moment matrices, checks the domain inequalities using
rational squares, and verifies VY<=R<=(4/3)VY exactly. It stores no
rounded approximation to a singular modulus. The all-index identities
above follow algebraically; no limit is inferred from these tests.
This new modular family identification has not been formalized in Lean.
