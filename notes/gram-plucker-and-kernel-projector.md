# Gram comparison and an integral projector for the content

The actual cancellation lattice is
Lambda_n={w in Z^3:x_n*w=0}. Its reduced basis a,b has lengths
lambda_1<=lambda_2. The content Gamma_n belongs to the coefficient
map F_n with rows y_n and z_n restricted to Lambda_n. These are
different objects: the Gram matrix of the full period-coordinate
matrix is not the Gram matrix of this integer kernel basis.

This note applies the proposed Gram and Grassmannian methods exactly,
and constructs an integral projector giving the content without a
division of minors after specialization. The required content-to-length
growth rate is still unproved. All arguments below are algebraic;
no finite family indices are sampled.

## What min-max proves for the relevant Gram matrix

Write

\[
 G=\begin{pmatrix}A&B\\B&C\end{pmatrix},\qquad
 A=\|a\|_2^2,\ B=a\cdot b,\ C=\|b\|_2^2.
\]

Gauss reduction gives 1<=A<=C and abs(B)<=A/2. For every real s,t,

\[
 |2Bst|\le A|st|\le\tfrac12(A s^2+A t^2)
                      \le\tfrac12(A s^2+C t^2).
\]

Hence G lies between one half and three halves of diag(A,C) in
the order on quadratic forms. The Rayleigh-quotient characterization
therefore gives the exact comparisons

\[
 A/2\le\mu_{\min}(G)\le A,\qquad
 C\le\mu_{\max}(G)\le3C/2.                                  \tag{1}
\]

The upper and lower comparisons in the opposite directions follow
by testing the coordinate vectors. In particular a lower eigenvalue
bound at the required scale is a lower bound for A, the squared
shortest nonzero integer relation. Positivity alone does not supply it.
For reference, see the variational eigenvalue characterization in
[Cornell's matrix-computations lecture](https://www.cs.cornell.edu/courses/cs6210/2025fa/lec/2025-11-03.html).

The trace formulation of the remaining joint target is especially
simple. Since C<=tr(G)<=2C,

\[
 \frac12\left(\frac\Gamma{\lambda_2}\right)^2
 \le\frac{\Gamma^2}{\operatorname{tr}G}
 \le\left(\frac\Gamma{\lambda_2}\right)^2.                    \tag{2}
\]

Thus their logarithmic rates agree up to the factor two. It would
suffice to prove

\[
 \liminf_{n\to\infty,\ n\text{ even}}
 \frac1n\log\frac{\Gamma_n^2}{\operatorname{tr}G_n}
                         >2(5-\log140).
\]

For example Gamma_n^2>=exp(0.12*n)*tr(G_n) along an unbounded
subsequence is sufficient for the proved positive-rounding construction.
Equation (2) proves the comparison, not this rate bound.

## The Grassmannian in this construction

The two-dimensional cancellation plane lies in a three-dimensional
space. Every nonzero element of wedge^2(R^3) is decomposable, so
Gr(2,3) is the whole projective plane in its Plucker coordinates.
For an elementary proof, a triple (p,q,r) with p nonzero is the
two-by-two minor triple of the two rows

\[
 (1,0,-r/p),\qquad(0,p,q).
\]

Their minors in columns 01,02,12 are p,q,r. The other cases follow
by permuting coordinates. Thus there is no further independent
quadratic Plucker equation for this ambient space.

For an integer kernel basis, the Plucker vector is already known:
a cross b=plus or minus x_n/g_n. Its Euclidean norm determines the
area lambda_1*lambda_2*sin(theta), not the separate basis lengths.
Projective Plucker coordinates also remove common scalar factors;
the index measured by Gamma_n belongs to the integral coefficient
map, not just to the real plane.

The determinant identity for the original columns gives the direction
of the associated divisibility. Let T be the gcd of all coordinates
of x cross y and x cross z, so T=g_n*Gamma_n. Then

\[
 (x\mathbin{\times}y)\mathbin{\times}(x\mathbin{\times}z)
                         =\det[x,y,z]\,x.
\]

Since T^2 divides each left-hand coordinate, Bezout for the coordinates
of x proves

\[
                g_n\Gamma_n^2\mid\det[x,y,z].                 \tag{3}
\]

For a nonzero determinant this bounds Gamma_n from above. It does
not provide the required lower bound.

One analytic family shows why a compact real-plane limit is not
enough. For any integer t>=2 take

\[
 x=(t,-t,1),\quad a=(1,1,0),\quad b=(0,1,t),\quad
 y=(1,0,0),\quad z=(0,0,1).
\]

The cross product a cross b equals the primitive normal x, so a,b
are a saturated kernel basis. They are Gauss-reduced, with

\[
 G=\begin{pmatrix}2&1\\1&t^2+1\end{pmatrix},\quad
 \lambda_2=\sqrt{t^2+1},\quad R=(t+1)/t.
\]

The two coefficient images are (1,0) and (0,t), so Gamma=1.
Every entry of G is positive and its smaller eigenvalue is at
least one. The planes converge projectively as t tends to infinity,
whereas Gamma/lambda_2 tends to zero. This is not the Apéry family;
it demonstrates that the geometric claims alone cannot prove the
missing inequality for that family. Further arithmetic identities
of the actual coefficients are essential.

## A global integral projector incorporates the gcd division

Put ell=x_n/g_n. Since ell is a primitive integer row, choose an
integer column u with ell*u=1 by Bezout. Define

\[
                   \Pi=I-u\ell.
\]

All entries are integers. Direct multiplication proves

\[
             \Pi^2=\Pi,\qquad\ell\Pi=0,\qquad
             \Pi w=w\quad(\ell w=0).
\]

Consequently Pi(Z^3)=Lambda_n, exactly and with saturation. If
F_n is the two-by-three matrix with rows y_n,z_n, then

\[
               F_n\Pi(\mathbb Z^3)=F_n(\Lambda_n).
\]

The content of the latter image is Gamma_n. We therefore obtain the
all-index integer identity

\[
 \boxed{\Gamma_n=
 \gcd_{i=0,1,2}\bigl(y_i-\ell_i(y\cdot u),\,
                         z_i-\ell_i(z\cdot u)\bigr).}         \tag{4}
\]

There is no division by g_n in (4), since ell was made primitive
before projection. The gcd is independent of the Bezout column u:
every such projector has the same image. This is an explicit integral
module construction, rather than an assumption about a filtered
annihilating ideal.

Locally the formula becomes shorter. For each prime p choose r with
ell_r a unit in Z_(p), and use u=e_r/ell_r. This is a local, not
necessarily integer, projector. Its kernel generators for i not r are
e_i-(ell_i/ell_r)*e_r. Thus

\[
 \boxed{v_p(\Gamma_n)=\min_{i\ne r}
 \{v_p(\ell_r y_i-\ell_i y_r),\,
                  v_p(\ell_r z_i-\ell_i z_r)\}.}              \tag{5}
\]

To justify localization, the primitive row map Z^3->Z is split by
the Bezout column, so its kernel localizes to the full kernel over
Z_(p). The unit factor ell_r does not change the valuations. Formula
(5) incorporates the entire lower-row gcd, including exceptional
extra powers, and reduces the local estimate to four normalized
residues. It does not prove those residues vanish to the required
higher orders.

A saddle-point estimate for the original coefficients would not by
itself evaluate either the integer content (4) or the shortest-vector
optimization defining G_n. No common contour representation of
Gamma_n and lambda_(2,n) has been constructed. Prefactor cancellation
for the original sums therefore is not a proved estimate for their
arithmetic ratio.

Equations (1)-(5) are proved above. They clarify the available Gram
and Grassmannian information and give a more direct local arithmetic
representation of the content. The strict lower growth rate in (2)
is still unproved, and the irrationality theorem remains incomplete.
No finite-index tests or Lean/TeX compilation were performed here.
