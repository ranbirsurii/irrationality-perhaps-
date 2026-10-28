# Applying duality and Gauss reduction to the new proposals

The new attachment suggests dual lattices, Gauss reduction, symplectic
relations, and several spectral and arithmetic constructions. The first
two give a concrete exact calculation for our coefficient lattice. They
do not yet give its all-index growth bound. The supplied text is treated
as a list of proposed methods, not as an established theorem or an
instruction to assume its asserted inequalities.
Here the Euclidean normalization cost is norm(w)/h(w); the full
integer-form majorant still includes the factor D=d_n^s and the raw
sum bound. Neither factor is removed by the duality calculation.

## Correct planar transference

For a Euclidean planar lattice L of covolume d, let J be rotation through
a right angle. An oriented basis u,v of determinant d has dual basis
-Jv/d,Ju/d. Since (-v,u) is another integral basis, this proves

  L* = (1/d) J L,
  lambda_i(L*)=lambda_i(L)/d, i=1,2.

For a Gauss-reduced basis realizing the two successive minima,
d=lambda_1 lambda_2 sin(theta) and sqrt(3)/2<=sin(theta)<=1. Therefore

  1 <= lambda_1(L*) lambda_2(L) <= 2/sqrt(3),
  1/lambda_1(L*) <= lambda_2(L) <= 2/(sqrt(3) lambda_1(L*)).

The proposal's upper bound by one has the inequality in the wrong
direction. For example the reduced basis (2,0),(1,2) has minima 2,sqrt(5)
and covolume 4, so its transference product is sqrt(5)/2>1. The angle
factor also explains why lambda_1 lambda_2=covolume is not a general
identity. This correction preserves the duality method, with the sharp
planar constant. General dual-lattice and transference statements are
given in [Waldschmidt's lecture notes](https://webusers.imj-prg.fr/~michel.waldschmidt/articles/pdf/GeometryNumbers2VI.pdf),
slides 27 and 30; the sharper planar formula has been derived above.

## The exact dual for our family

Let Lambda=ker_Z C have integral basis a,b and Gram matrix

  G=[[A,B],[B,C0]], H^2=A C0-B^2.

To distinguish the Gram entry C0 from the lower-period matrix C, write
the coefficient map on this basis as

  K=[[y_a,y_b],[z_a,z_b]], delta=det(K)!=0.

The rank proof supplies the determinant condition at every eligible
index. The rational coefficient lattice L=F^(-1)Z^2 has coordinates
K^(-1)Z^2, with the metric G. If P_V denotes orthogonal projection to
the cancellation plane, its dual is exactly

  L* = Z P_V Y + Z P_V Z.

Indeed the adjoint of F sends the standard integer basis to the two
projected coefficient rows. A vector pairs integrally with F^(-1)Z^2
precisely when it is the adjoint image of an integer vector. In basis
coordinates that adjoint embedding is G^(-1)K^T, so the dual Gram matrix is

  K G^(-1) K^T = S/H^2, S=K adj(G) K^T.

The matrix S has integer entries and is positive definite. Explicitly,

  S11=C0 y_a^2-2B y_a y_b+A y_b^2,
  S12=C0 y_a z_a-B(y_a z_b+y_b z_a)+A y_b z_b,
  S22=C0 z_a^2-2B z_a z_b+A z_b^2.

Its determinant is delta^2 H^2. Thus the new task can be written
without either kappa or an unspecified geometric object:

  lambda_1(L*)^2 = min_{(p,q) in Z^2 minus (0,0)}
        (S11 p^2+2S12 pq+S22 q^2)/H^2.

At a fixed weight s, a lower exponential rate for lambda_1(L*) strictly
greater than -(a_s-s) is sufficient for the required primitive-cost rate.
No such uniform lower bound is assumed here.

## Exact integer reduction gives the optimal primitive cost

Choose U in GL_2(Z) Gauss-reducing the integral form S:

  U^T S U=[[mu,beta],[beta,nu]], 0<mu<=nu, 2 abs(beta)<=mu.

The minimum of this form on nonzero integer pairs is mu, and its second
Euclidean lattice minimum squared is nu. For the first assertion, if both
coordinates are nonzero the form is at least mu(p^2+q^2)/2>=mu; if one
coordinate is zero, the same lower bound follows directly. For the
second, the first basis vector realizes mu, while any independent vector
has nonzero second coordinate. If its absolute value is one, minimizing
over the first coordinate and 2 abs(beta)<=mu gives a value at least nu.
If its absolute value is at least two, completing the square gives a
value at least 4(nu-beta^2/mu)>=3nu>=nu. Thus the second basis vector
realizes the second minimum.

The primal integer Gram matrix from the explicit coefficient preimages is

  T=adj(K)^T G adj(K)=adj(S)=[[S22,-S12],[-S12,S11]].

The equality follows from the adjugate product identity and the fact that
the adjugate operation is an involution on two-by-two matrices. Also
adj(S)=J^T S J, so T and S are integrally equivalent and have the same
two minimum values mu,nu. Dividing the primal basis by delta gives L.
Consequently the optimal independent-pair primitive Euclidean cost is
exactly

  lambda_2(L)^2 = nu/delta^2,
  lambda_1(L*)^2 = mu/H^2.

This is an explicit algorithm on three integers, with an exact unimodular
witness. It combines the duality and Gauss-reduction proposals directly.
The all-index estimate is now the precise inequality

  limsup (log(nu_n)-2 log(abs(delta_n)))/(2n) < a_s-s.

The integer reduction algorithm does not prove that estimate by its
existence or its polynomial running time.

## A valid content shortcut and what the existing records say

Let eta=gcd(S11,2S12,S22)>0. Every positive value of the integer form is
a positive multiple of eta, so

  lambda_1(L*) >= sqrt(eta)/H,
  lambda_2(L) <= 2H/sqrt(3 eta).

This is an unconditional upper bound, but it can be much weaker than
using the actual minimum mu. The new script `check_dual_cost_reduction.py`
reuses only the existing stored weight-five indices 20,80,1280. It checks
the two Gram constructions, their determinant identity, exact Gauss
reduction with a unimodular witness, and the following exact comparisons:

  nu/delta^2 < C0/Gamma^2 < 4H^2/(3 eta).

Thus in all three specified records the fully reduced coefficient lattice
strictly improves the old common-content bound, whereas the simple
quadratic-content shortcut is strictly worse. These are finite exact
comparisons, not a limiting theorem. No new family indices or period
coefficients were generated. The reproducible witness data are in
`dual-cost-reduction-checks.json`.

## What the other structural suggestions would need

Gauss reduction, LLL angle bounds, bounded covolume, or a symplectic
structure do not alone bound a lattice's aspect ratio. The determinant-one
family generated by (2^n,0),(0,2^(-n)) is orthogonal and already reduced,
has covolume one, and is obtained by symplectic transformations, but its
second minimum is 2^n and its aspect ratio is 4^n. This is a general
counterexample to the automatic inference, not a claim about our kernels.

Conversely the unimodular shear [[1,N],[0,1]] can have a poorly conditioned
displayed basis while its lattice is still Z^2. QR, Cholesky, and transfer
spectra must therefore be related to the intrinsic reduced lattice rather
than an arbitrary frame.

The degree-33 bridge mentioned in the proposals is already an exact
polynomial-cost identity in `smith-exterior-square-progress.md`. Its
pointwise denominator bound does not give the reduced-form minimum above.
If transfers are iterated, their cumulative denominators and cancellations
must also be accounted for.

The Frobenius, Robba-ring, arithmetic-height, and motivic suggestions would
need an explicit identification yielding a lower bound for the displayed
integer quadratic-form minimum, or an equivalent normalized estimate.
The new list does not contain such an identification. The strongest new
concrete route here is the exact dual-form reduction; its required
asymptotic inequality remains unproved. No new unconditional odd-zeta
irrationality conclusion or complete Lean verification is claimed.
