# An exact root formula and adjugate polynomial pencil

This is an explicit formula for the existing odd-zeta forms, not a
claim of an unconditional irrationality proof.

## Laurent coefficients directly from the kernel roots

Let Q(t)=product_(h=0..n)(t+h), xi_h=-h, and

    N_m(t)=(n!)^s/(m!)^2 product_(v=1..m)(t-v)(t+n+v).

The numerator roots are rho=v and rho=-n-v, each once. No numerator
root equals a pole xi_h. Define

    L_h=N_m(xi_h)/Q'(xi_h)^s,
    p_(ell,h)=(-1)^(ell-1)/ell
       *[sum_rho (xi_h-rho)^(-ell)
                      -s sum_(j!=h)(xi_h-xi_j)^(-ell)].

The complete finite root formula for the order-k Laurent coefficient is

    A_(k,h)=L_h sum_(e_1+2e_2+...+u e_u=u)
                         product_(ell=1..u) p_(ell,h)^e_ell/e_ell!,
    u=s-k.                                                     (1)

The empty partition at u=0 contributes one. To prove (1), factor

    (t-xi_h)^s T(t)=L_h
       product_rho[1+(t-xi_h)/(xi_h-rho)]
       product_(j!=h)[1+(t-xi_h)/(xi_h-xi_j)]^(-s).

Its formal logarithm, after removing L_h, is sum_(ell>=1)
p_(ell,h)(t-xi_h)^ell. Exponentiating and extracting degree u proves
(1). This is a formal power-series identity over Q, so there are no
choices of analytic logarithm or contour. Summing A_(k,h) gives each
period row, and -sum_(h,k) A_(k,h)H_(h,k) gives the rational row.
Thus every entry of the augmented coefficient matrix is an explicit
finite expression in integer root differences and factorials.

## The adjugate gives a polynomial vector in a new variable

Let Phi be the rational augmented matrix with rows lower periods,
target zeta(s), and rational term. Let B=D Phi, D=d_n^s, and
Delta=det B, which is nonzero by the established augmented-rank result.
With t and c denoting the target and constant row indices, put

    U=adj(B)e_t, V=adj(B)e_c, W(X)=X U+V.

The exact polynomial identity is

    B W(X)=Delta(0,...,0,X,1)^T.                              (2)

Every entry of U and V is a signed minor whose entries are given by
(1). Consequently (1)-(2) are a finite root-and-cofactor formula for
the cancellation weights at every weight and index.

For any integers p,q, not both zero, w=pU+qV is integral, annihilates
all lower-period rows, and has coefficient pair Delta(p,q). Its own
coefficient content is exactly

    h(w)=abs(Delta) gcd(p,q).                                (3)

For coprime p,q, its primitive form is sign(Delta)(p zeta(s)+q).
If S is the maximum absolute raw block sum, its analytic majorant is

    D S norm_1(pU+qV)/abs(Delta)
      =S norm_1(Phi^(-1)(0,...,0,p,q)^T).                     (4)

Indeed adj(D Phi)=D^r adj(Phi) and det(D Phi)=D^(r+1)det(Phi).
The scalar D cancels exactly in (4). The arithmetic size remains in
the inverse matrix; the identity does not prove that inverse small.
Unlike a shared Gamma normalization, (3) evaluates the content of
each chosen adjugate vector exactly.

## Roots of the coefficient polynomials and their dispersion

If U_j!=0, the root of W_j(X) is the explicit rational number
eta_j=-V_j/U_j. For q>0 there is an exact identity

    norm_1(pU+qV)
      =q sum_(U_j!=0) abs(U_j) abs(p/q-eta_j)
         +q sum_(U_j=0) abs(V_j).                            (5)

Thus the coefficient cost is a weighted distance from a rational slope
to the cofactor roots. A weighted median of the eta_j minimizes this
distance over real slopes: between roots its slope is the weight to
the left minus the weight to the right, and a median is where that
slope changes from nonpositive to nonnegative. Rational slopes must
also pay their denominator q, as displayed in (5).

For two nonzero U_i,U_j the root separation is exactly

    eta_i-eta_j=(U_i V_j-U_j V_i)/(U_i U_j).                  (6)

Consequently the adjugate approach isolates a concrete quantitative
target: control the weighted root dispersion and the integer slope
height simultaneously after division by abs(Delta). Taking absolute
cofactor bounds separately discards precisely this correlation.

Taking U or V alone gives the primitive forms zeta(s) and 1 (up to
sign). Their majorants therefore cannot tend to zero. A decay proof
must use suitable mixed integer pairs p,q and establish nonvanishing;
no such all-index choice or decay estimate is asserted here.

## Verification scope

Jacobi's complementary-minor identity sharpens (6). Let C be the first
r-1 rows of B and C^(ij) the square matrix after deleting columns i,j.
For i<j,

    U_i V_j-U_j V_i=(-1)^(i+j+1) Delta det C^(ij).             (7)

This follows by applying the complementary-minor identity to the two
last columns of adj(B); its sign is (-1)^(i+j+(r-1)+r).
For a root indexed by k with U_k!=0, take

    g_k=gcd(U_k,V_k), p=-V_k/g_k, q=U_k/g_k.

The pair is primitive, w_k=0, and (7) proves the exact cost formula

    norm_1(pU+qV)/abs(Delta)
       =sum_(j!=k) abs(det C^(jk))/g_k.                       (8)

Thus the root choice reproduces a sparse Cramer vector, with its own
normalizing gcd evaluated exactly. This is an identification with that
construction, not an additional independent gcd saving. To force decay
one still needs a sufficiently small value of D S times (8), together
with nonvanishing or a suitable independent pair.

The exact script roots_adjugate_formula.py checks six actual profiles
at weights 7,9,11. The root-partition formula is compared with the
independent harmonic logarithmic-jet formula, and 24 adjugate image,
coefficient-content and weighted-root-mass identities pass. It also
checks 53 complementary-minor identities and 28 exact primitive root
costs. The Lean
theorem integer_adjugate_vector_image verifies (2) for arbitrary integer
square matrices and vectors. The root-partition identity and full
family identification above are paper proofs; no additional negative
cost rate or irrationality endpoint is claimed.
