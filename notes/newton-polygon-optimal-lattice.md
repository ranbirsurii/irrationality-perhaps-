# Newton polygons and the optimal local lattice

This continuation uses no new finite computations. Its purpose is to
replace entrywise denominator bounds by the exact invariant and explain
which lattice changes can sharpen those bounds without changing the
polynomial being evaluated.

## Exact primitive denominator

Let P(X)=det(XI-A) be monic over Q, of degree h. For each prime p write

    D_p(P) = -min_(0<=j<=h) v_p([X^j]P), with v_p(0)=infinity.

Since the leading coefficient is one, D_p is a nonnegative integer.
If d(P) is the least positive integer clearing all coefficients, then

    v_p(d(P))=D_p(P).

The Newton polygon is the lower convex hull of the points
(j,v_p([X^j]P)). Its minimum height is the minimum coefficient valuation.
Thus D_p is its depth below height zero. It is not the area under the
polygon. With slopes counted by their horizontal multiplicities, it is
also the sum of their positive parts: the polygon ends at (h,0).

Equivalently, let lambda_i be the valuations of the roots in a splitting
field, counted with multiplicity, giving the value infinity to zero
roots. The Newton polygon root theorem, or multiplicativity of the
nonarchimedean Gauss norm applied to the linear factors, proves

    D_p(P)=sum_i max(0,-lambda_i).

There is no unproved cancellation hypothesis in this equality. It is
exact for the characteristic polynomial, unlike a bound using the
singular factors of a particular matrix presentation.

## An optimization theorem that explains how to remove overpayment

Let V be a finite-dimensional Q_p-vector space and A an endomorphism.
For every full Z_p lattice Lambda in V set

    T_A(Lambda)=length_Zp((Lambda+A Lambda)/Lambda).

Then

    min_(full lattices Lambda) T_A(Lambda)
      = D_p(det(XI-A)).                                     (1)

In particular the minimum is attained. This is an algebraic existence
theorem, not an effective construction of an optimal Hankel lattice.

Proof of the lower bound. In a basis of Lambda, take the Smith exponents
e_1<=...<=e_r of A, omitting zero diagonal factors (equivalently assigning
them exponent infinity). Left and right Smith transformations are
unimodular and preserve Lambda. Hence

    T_A(Lambda)=sum_i max(0,-e_i).

Every q-minor of A has valuation at least the sum of its q smallest
Smith exponents. Every characteristic coefficient is a sum of such
principal minors. Therefore all characteristic coefficients have
valuation at least -T_A(Lambda). This proves D_p<=T_A(Lambda).

Proof of attainment. Factor the characteristic polynomial over Q_p into
the coprime monic factors whose roots have respectively nonnegative
and negative valuations. These factors belong to Q_p[X], since the
valuation is invariant under the local Galois group. Their primary
decomposition gives V=V_+ direct-sum V_- and corresponding restrictions
A_+,A_-. The first characteristic polynomial is integral; the inverse
A_-^(-1) also has integral characteristic polynomial.

Any endomorphism T with integral characteristic polynomial has a stable
full lattice. Indeed, start with any full lattice L0 and take

    L0+T L0+...+T^(d-1)L0.

Cayley-Hamilton makes this lattice T-stable. Apply the construction to
A_+ and to A_-^(-1), obtaining lattices L_+ and L_-. Then

    A_+ L_+ subset L_+, and L_- subset A_- L_-.

For Lambda=L_+ direct-sum L_- the first summand contributes zero and
the second contributes -v_p(det A_-). This is precisely the sum of the
negative root valuations with their signs reversed, proving (1).

## Application to the powered Hankel pencil

Write the actual rational moment pencil as G_(s,K)(X)=C_(s,K)+X B_(s,K),
where B is invertible. Its monic normalization is

    P_(s,K)(X)=det(XI+B^(-1)C).

Apply (1) to A=-B^(-1)C. It is permissible to change the entire local
lattice by rational conjugation when estimating this characteristic
polynomial: the polynomial is unchanged. This can sharply improve a
Smith bound computed in the original basis. Merely changing an integral
basis of that same lattice cannot improve T_A.

The proposed clean route is to use the pole/collision filtration to
construct a lattice with small T_A directly. One can allow A to preserve
a large part of the lattice and charge only the quotient on which it
expands. That is more precise than charging every matrix entry or every
negative Smith factor in an arbitrary original basis.

However, constructing the minimizing lattice by first computing the
unknown slope decomposition does not prove a new bound on D_p. To
obtain an estimate it must instead be constructed from the explicit
factorial, harmonic, and collision data, with its quotient length bounded
independently. No such middle-band construction is proved here.

The exact remaining comparison for the weight-five transfer is

    limsup K^(-2) sum_p (D_p(P_(s,K))-D_p(P_(5,K))) log p < epsilon_5,

with epsilon_5 supplied by the specific verified weight-five decay
bound. Equivalently, one must compare the optimal local quotient lengths
in (1). Separate upper bounds for the two lengths cannot be subtracted
to prove this inequality.

Strict positivity at zeta(s) gives nonvanishing of the final integer
polynomial. It does not constrain its local Newton depth. Accordingly,
the optimal-lattice theorem does not itself establish irrationality.
No finite data, random-slope assumption, or unproved sextic mean-value
estimate is used in this note.

## Sources and formal scope

The Newton polygon/root valuation theorem is reviewed in the primary
lecture notes of Romyar Sharifi, Algebraic Number Theory, Chapter 5:
https://www.math.ucla.edu/~sharifi/notes/algnum-ch05.html

For characteristic polynomials, matrix precision and Newton/Hodge
comparisons see Caruso, Roe and Vaccon, Characteristic Polynomials of
p-adic Matrices:
https://arxiv.org/abs/1702.01653

The proofs above are paper arguments. They have not been added as axioms
or represented as a completed Lean formalization. The uniform Hankel
Newton-depth comparison and the final odd-zeta theorem remain unproved.
