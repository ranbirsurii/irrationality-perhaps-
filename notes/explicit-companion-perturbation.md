# Explicit nilpotent and rank-one constructions for every Hankel index

No finite arithmetic experiments are used here.

Let h=K-N>=1 and let P_s(X)=Delta_s(X)/L_s be the actual monic
Hankel polynomial. Write

    P_s(X)=X^h+a_(s,h-1)X^(h-1)+...+a_(s,0).

Every a_(s,j) is the explicitly defined rational coefficient
[X^j]Delta_s/L_s. This construction requires no knowledge of zeta(s),
no eigenvalue computation, and no cyclicity assertion about the original
matrix. We replace its matrix representation by the companion matrix of
the same polynomial; we do not assert that the two matrices are similar.

## Construction of the nilpotent part and the rank-one remainder

In the basis e_0,...,e_(h-1), put

    J e_i=e_(i+1) for i<h-1, and J e_(h-1)=0,
    a_s=(a_(s,0),...,a_(s,h-1))^T,
    C_s=J-a_s e_(h-1)^T.

Thus C_s has ones on the subdiagonal and last column -a_s. By construction
J^h=0 and charpoly(C_s)=P_s. A direct proof of the latter follows below.

Work in the field Q_p(X), and define

    N=-X^(-1)J,
    R_s=X^(-1)a_s e_(h-1)^T.

Then N^h=0, rank(R_s)<=1, and

    XI-C_s=X(I+N+R_s).

The nilpotent contraction is completely explicit:

    (I+N)^(-1)=sum_(k=0..h-1) X^(-k)J^k.

Consequently the post-contraction remainder is

    W_s=(I+N)^(-1)R_s
       =sum_(k=0..h-1) X^(-k-1)J^k a_s e_(h-1)^T,         (1)

which still has rank at most one. This supplies the N and R requested
in the previous relative-perturbation argument at every index.

The rank-one determinant identity det(I+u v^T)=1+v^T u gives

    det(XI-C_s)
      =X^h(1+sum_(k=0..h-1) X^(-k-1)a_(s,h-1-k))
      =X^h+sum_(j=0..h-1) a_(s,j)X^j=P_s(X).              (2)

Here det(I+N)=1 because N is nilpotent. This also proves the companion
characteristic-polynomial identity with the precise sign convention used.

## A rank-one relative perturbation of weight five

For weights s and five at the same K,N,h, the same shift J is used.
Therefore

    C_s-C_5=-(a_s-a_5)e_(h-1)^T.

The actual polynomial ratio is represented by the rank-one matrix

    E_(s,5)=(XI-C_5)^(-1)(a_s-a_5)e_(h-1)^T.

The inverse exists over Q_p(X), since P_5 is monic and nonzero.
The determinant identity is

    P_s/P_5=det(I+E_(s,5))
           =1+e_(h-1)^T(XI-C_5)^(-1)(a_s-a_5).             (3)

Thus no low-rank hypothesis about the difference of the original
moment matrices is needed. Rank one is available after replacing both
matrices by polynomial-equivalent companion representations.

## What the constructed remainder costs

Let beta_(s,5) be the scalar after 1 in (3). Exactly,

    beta_(s,5)=(P_s-P_5)/P_5.

For the Gauss valuation,

    D_p(P_s)-D_p(P_5)=-v_G(1+beta_(s,5)).                  (4)

If v_G(beta)>=0, the local extra denominator cost is nonpositive.
If v_G(beta)>0, it is exactly zero. If v_G(beta)<0, it equals
-v_G(beta). These conclusions follow from the nonarchimedean triangle
inequality, with equality when the two summands have different valuations.

The important limitation of the construction is explicit in (1)-(2).
Its scalar feedback contains the original coefficients a_(s,j):

    1+sum_(j=0..h-1)a_(s,j)X^(j-h).

These monomials have different degrees. Their Gauss valuation is exactly
min(0,min_j v_p(a_(s,j))). Thus reducing the remainder to rank one does
not bound its amplitude. The original Newton depth is preserved exactly,
as it must be when the polynomial itself is preserved.

We have therefore constructed the nilpotent part, the rank-one
post-contraction remainder, and the rank-one weight-five comparison.
We have not established the uniform Gauss-valuation estimate on the
scalar in (3) that would finish the irrationality proof. Neither the
rank-one property nor the nilpotent contraction is substituted for
that estimate. This is a paper construction, not a new Lean axiom or
a claim of a completed formalization of the Hankel family.
