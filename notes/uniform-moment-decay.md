# Uniform analytic decay of the complete moment certificates

Fix any r>=3, s=2r+1, and even n>=4r. Use the original common kernel
T_n=T_(s,n,n-r) and w_n(t)=t(t+n)/(12n^2). Write

    J_(ell,n)=sum_(k>n-r) T_n(k) w_n(k)^ell,  0<=ell<=2r,
    a_s=(1/100)16^(-(s-7)),  b_s=(27/100)16^(-(s-7)).

The previous kernel transition proves J_(0,n+2)<=a_s J_(0,n).
We now prove the all-moment version

    J_(ell,n+2)<=b_s J_(ell,n)  for every 0<=ell<=2r.

Indeed k>=n-r+1>=3n/4, and exact division gives

    w_(n+2)(k+2)/w_n(k)
      = (n/(n+2))^2 (1+2/k)(1+4/(k+n))
      <= exp(8/(3n)+16/(7n)) < exp(5/n).

Raising to ell<=2r costs at most exp(10r/n)<=exp(5/2)<27.
Multiply by the proved kernel transition bound and sum after the bijection
k->k+2 of the complete summation ranges. Every moment converges by the
previous power-tail estimates. No boundary term is omitted.

Let n0=4r and j=(n-n0)/2. Iteration proves

    J_(0,n)<=a_s^j J_(0,n0),
    J_(ell,n)<=b_s^j J_(ell,n0).

For the true moment Gram matrix H_n=(J_(i+j,n)), its trace therefore
satisfies tr(H_n)<=b_s^j tr(H_n0). This trace bound does not assert an
entrywise-to-Loewner implication: such an implication would be invalid
for arbitrary signed vectors. Instead positive semidefiniteness gives
z^T H_n z<=tr(H_n)||z||_2^2 for every real coefficient vector z.

## The computable certificates retain this decay

The stored mass certificate is mu_n=c_0+t_0. With K=3n, the exact tail
formula gives t_0=K*T_n(K)/(4r+1). Since T_n(K)<=J_(0,n),

    mu_n <= (1+3n/(4r+1)) J_(0,n)
          <= (1+3n/(4r+1)) a_s^j J_(0,n0).

The stored matrix G_n has diagonal c_(2i)+(r+1)t_(2i).
Because w_n(K)=1 exactly, t_(2i)=K*T_n(K)/(4r+1-4i).
Every denominator is at least one. Summing these r+1 diagonal terms gives

    tr(G_n) <= tr(H_n)+3n(r+1)^2 J_(0,n)
             <= b_s^j [tr(H_n0)+3n(r+1)^2 J_(0,n0)].

Thus neither the finite cutoff nor the diagonal tail certificate destroys
the geometric decay. Their explicit losses are only polynomial in n
at each fixed weight. All starting moments are finite, positive constants.

## Consequence for every profile

For any real weighted polynomial profile z_n at the eligible index n,
the previously established moment bound and the trace estimate give

    |L_n|^2 <= mu_n tr(G_n) ||z_n||_2^2
             <= C_r (n+1)^2 (a_s*b_s)^j ||z_n||_2^2,

where a valid positive constant is

    C_r=3(r+1)^2 J_(0,n0) [tr(H_n0)+J_(0,n0)].

To check this constant, use 1+3n/(4r+1)<=n+1 and
tr(H_n0)+3n(r+1)^2 J_(0,n0)
<=3(r+1)^2(n+1)[tr(H_n0)+J_(0,n0)].
This is a proved clean analytic majorant for every form, with its actual
profile size retained. In particular profiles satisfying

    ||z_n||_2 <= C exp(gamma*(n-n0)),
    gamma < -(1/4) log(a_s*b_s),

give forms tending to zero. The factor 1/4 comes from j=(n-n0)/2 and
the squared profile norm. It is not an assertion that our primitive
profiles satisfy that bound. The mass and Gram parts now have proved
decay; the varying inverse-coefficient profiles are still part of the
same original target, not an extra hypothesis appended to a theorem.

For the two selected primitive pairs, take z_n=F_raw,n U_n e_i.
No estimate at the required rate for these varying vectors is established
by this note. Consequently no unconditional irrationality conclusion
is drawn. These are paper proofs, not yet a Lean formalization of the
actual rational family.

`analytic_kernel_transition.py` checks the pointwise weighted multiplier
at all moment orders 0,...,2r in its higher-index examples, using exact
fractions. The all-index proof is the inequality argument above, not
an extrapolation from those tests.

## Scope of covolume optimization

Primitive pair optimization and a local reduced basis correctly avoid
the need to prescribe one particular gcd-based pair. However covolume
alone gives no upper bound on the second minimum. For T>=1 the lattice
diag(1/T,T) Z^2 has covolume one, a Gauss-reduced orthogonal basis, and
successive minima 1/T and T. Its second minimum is unbounded.

The valid reduced-basis bound is

    lambda_1 lambda_2 <= (2/sqrt(3)) covol(L),

because the reduced-basis angle has sine at least sqrt(3)/2. An upper
bound for lambda_2 alone consequently requires further information
about lambda_1, or an actual estimate for the reduced second coefficient.
A Casoratian formula for the covolume is useful determinant data but
does not by itself prove the proposed second-minimum upper bound.
