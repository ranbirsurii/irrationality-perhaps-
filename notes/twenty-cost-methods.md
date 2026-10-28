# Twenty approaches to the primitive cost

This comparison concerns the actual consecutive-block family, not an
arbitrary period space. The augmented-rank proof is already available.
The remaining task is a quantitative arithmetic estimate. None of the
twenty routes below has supplied that estimate in this project. The
chosen route gives an exact, less restrictive optimization problem; it
is not represented as a completed irrationality proof.

Fix s=2r+1, N=r+1, D=d_n^s, and the established raw upper bound
S<=C_s(n+1)^12 exp(-a_s n), where
a_s=log(140)+(s-5)log(4). For integer w in the lower-period kernel,
write h(w)=gcd(Y(w),Z(w)). The primitive majorant is

  abs(L_w) <= D S norm(w)_1/h(w).

The Euclidean norm differs from the absolute mass by a factor between
one and sqrt(N), so the two costs have the same exponential budget at
each fixed weight. The required upper rate for norm(w)_2/h(w) is below
a_s-s. At weight seven this coarse budget is between 0.7142311 and
0.7142312. A fixed basis with both primitive costs below that rate is
sufficient; it is not necessary to prove a separate lower bound for Gamma.

## Comparison

| No. | Method | Precise arithmetic input or output | Assessment |
| --- | --- | --- | --- |
| 1 | Reduce the full coefficient preimage lattice | Optimize all primitive pairs through F^(-1)(Z^2), not just a,b divided by their individual gcds | Selected. The exact equivalence and its cost are proved below; the all-index second-minimum bound remains open here. |
| 2 | Individual gcd normalization on a chosen basis | Bound norm(a)^2/h(a)^2+norm(b)^2/h(b)^2 | Already proved as a sufficient reduction. Route 1 optimizes over a larger set. |
| 3 | Shared-content lattice reduction | Bound lambda_2(Lambda)/Gamma | Sufficient, but can miss extra selected-vector divisibility. |
| 4 | Bombieri-Vaaler or sharp Siegel bounds | Control both independent kernel vectors through determinant divisors and covolume | A volume estimate alone does not control the second minimum without shape information. |
| 5 | Smith or Hermite basis adapted to the coefficient image | Bound the ambient norms of the preimages, not just the integer invariant factors | Exact lattice identification is available; a short Smith witness has not been proved uniformly. |
| 6 | Higher-order local jet lifting | Prove the actual normalized minor congruences after dividing by the lower-row gcd | A direct way to prove content savings. Existing first-order collinearity does not supply the next powers. |
| 7 | Lucas and Kummer carry analysis | Sum explicit lower bounds for prime valuations of the normalized minors | Useful for factorial factors, but the determinant cancellations and subsequent gcd division still require proof. |
| 8 | Prime-product floor minima | Identify a nonzero floor-function factor for the actual determinant family | The known factor for a different factorial family is not an identification with our content. |
| 9 | Andrews transformations and denominator refinements | Derive integrality of these exact coefficient combinations from a verified multisum identity | No such identity for the actual selected minors was obtained. Clearing all rows by a smaller common scalar alone leaves the primitive cost invariant. |
| 10 | Fraction-free block recurrence | Track integral preimage lattices under every rational transfer matrix | The block recurrence transports vectors, but denominators in the transport must be counted. |
| 11 | Exterior-power or Casoratian transport | Obtain selected-minor divisibility, not merely full determinant growth | The full determinant can be nonzero and large while the required selected content is small. |
| 12 | Limiting companion spectra | Bound an actual norm recurrence and account for all integer normalizations | Perron growth does not determine a gcd or a lattice index. |
| 13 | Dwork or Frobenius supercongruences | Identify the kernels and integral structure, then prove the needed divisibility order | No Frobenius comparison proving the required normalized minors has been constructed here. |
| 14 | Mahler interpolation | Prove divisibility of the actual Mahler coefficients, including every low-order coefficient | Existence of the interpolation expansion does not imply those divisibilities. |
| 15 | Symmetry-group arithmetic savings | Construct a symmetry of this family with a denominator-saving valuation formula | Brown-Zudilin obtain arithmetic gains in a different cellular family; transferring them requires an explicit map. |
| 16 | Multi-point or multi-parameter Pade optimization | Recompute analytic decay, denominators, rank, and primitive cost together | A possible replacement family; no parameter choice proving the isolated target was found. |
| 17 | Saddle-point analysis after elimination | Bound the actual primitive combination, rather than multiplying a maximum raw sum by its mass | May capture extra cancellation, but requires an explicit combination and a nonzero leading term with arithmetic normalization included. |
| 18 | Moment or Christoffel-function bounds | Identify the normalized lattice Gram matrix with a positive moment problem with quantitative eigenvalue bounds | Rank and positivity alone are not that metric identification. |
| 19 | Invariant-cone or interval tail certificate | Prove an all-index recurrence and a forward-invariant inequality beyond an explicit threshold | Finite successes do not establish the invariant cone; no such certificate was proved for this cost sequence. |
| 20 | Integral geometric comparison and adelic metrics | Construct the actual integral frame and prove its height or metric distortion bound | A rational or motivic rank comparison alone does not bound the arithmetic distortion. |

These are candidate mechanisms, not twenty completed proofs or a claim
that the uncompleted mechanisms are impossible.

## The selected method: allow every primitive coefficient pair

Let Lambda=ker_Z C and choose any integral basis a,b. Put

  B = [[Y(a),Y(b)],[Z(a),Z(b)]], delta=det(B)!=0,
  V=span_R(Lambda), F(v)=(Y(v),Z(v)).

The rank theorem implies that F:V->R^2 is a linear isomorphism.
Define the rational lattice

  L = {v in span_Q(Lambda) : F(v) belongs to Z^2}.

In the coordinates a,b this is exactly B^(-1) Z^2. Thus L is a genuine
discrete rank-two lattice, even though its vectors need not have integer
ambient coordinates. The map F identifies L with Z^2. The original
Lambda is a sublattice of L, of index abs(delta), because its image is
B Z^2. If H is the covolume of Lambda in V, then

  covol(L)=H/abs(delta).

This formula uses the full coefficient determinant, not a gcd of
selected minors or a spectral radius.

### Exact primitive correspondence

For nonzero w in Lambda, the vector v=w/h(w) belongs to L and F(v) is
a primitive pair of integers. Conversely, take v in L with F(v) primitive.
Clear the rational coordinates of v by a positive integer t, so that
w=t*v belongs to Lambda. Then F(w)=t*F(v), and therefore h(w)=t.
Consequently w/h(w)=v exactly. No normalization cost has been discarded.

One may also make the converse entirely explicit. If F(v)=(u,z) is
primitive, in coordinates a,b take

  x = delta * adj(B) * (u,z).

This is an integer coordinate vector, B*x=delta^2*(u,z), and its output
gcd is delta^2. Dividing x by that gcd gives B^(-1)(u,z). This avoids
any ambiguity about the sign of delta.

### The exact optimum among independent pairs

Let lambda_2(L) be the second Euclidean successive minimum. Every pair
of independent integer kernel vectors w_1,w_2 gives independent primitive
vectors w_i/h(w_i) in L. Hence

  lambda_2(L) <= max_i norm(w_i)_2/h(w_i).

Conversely choose a Gauss-reduced basis u,v of the planar lattice L.
Its longer norm is lambda_2(L). Since F sends a lattice basis to a basis
of Z^2, both coefficient pairs are primitive and their determinant is
plus or minus one. The exact primitive correspondence realizes u,v by
integer kernel vectors and their own gcds. Thus

  min over independent w_1,w_2 of max_i norm(w_i)_2/h(w_i)
      = lambda_2(L).

This is an attained minimum, not merely an infimum. It shows precisely
which normalization problem must be optimized. In particular

  lambda_2(L) <= lambda_2(Lambda)/Gamma,
  lambda_2(L) <= max(norm(a)/h(a),norm(b)/h(b)).

The first inequality uses Lambda/Gamma contained in L, and the second
uses the two individually normalized basis vectors as competitors.

### The remaining estimate, without a surplus common-content requirement

The two primitive forms of the reduced basis of L have determinant plus
or minus one, so cannot both vanish. Both satisfy

  abs(L_i) <= sqrt(N) D S lambda_2(L).

Therefore the desired decay follows if

  limsup log(lambda_2(L_n))/n < a_s-s.

Equivalently, writing kappa(L)=lambda_2(L)/lambda_1(L), Gauss reduction
gives the sufficient bound

  lambda_2(L)^2 <= (2/sqrt(3))*kappa(L)*H/abs(delta).

The degree-count rank theorem proves delta!=0, but it does not prove
this normalized shape-and-covolume rate. That rate for the actual family
has not been established. The selected route removes unnecessary
restrictions from the optimization; it has not completed the theorem.

## Literature checked against the actual obligation

- [Krattenthaler-Rivoal, denominator conjecture](https://arxiv.org/abs/math/0311114)
  proves coefficient denominator results for specified hypergeometric
  families. An application here needs an exact identity for the selected
  forms and their determinant divisors; no such application is assumed.
- [Lai, 2025](https://arxiv.org/html/2501.05321v2), Lemma 3.3, uses a
  floor-minimum prime factor for its explicitly defined factorial kernel.
  The introduction and elimination theorem concern counts of irrational
  values, rather than irrationality of every specified odd value.
- [Brown-Zudilin, revised January 2026](https://arxiv.org/html/2210.03391v3)
  gives approximations with positive error less than q^(-0.86). This alone
  does not force nonzero integer linear forms to tend to zero: multiplying
  by q yields the upper bound q^(0.14), not a vanishing bound. A transfer
  to the present family and a stronger arithmetic rate would still be needed.
- [Zudilin, third-order recursion](https://arxiv.org/abs/math/0206178)
  supplies a specific recurrence construction for zeta five. A recurrence
  does not, without a normalization calculation, establish the primitive
  cost of this different consecutive-block family.

No result from an unrelated family is being promoted to the missing
cost estimate, and no claim of an unconditional all-odd proof is attached
to this comparison.
