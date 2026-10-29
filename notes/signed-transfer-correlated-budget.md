# Combining the signed transformation with the established recurrence

This calculation concerns the original weight-five three-block family
used in the definitions of H_n, Gamma_n, and epsilon. It applies the
previous construction to the signed Saalschutz decomposition, rather
than paying its absolute multiplier mass and branch maximum separately.
It proves a subexponential relative transfer and a correlated rate
identity. It does not prove a new sharp gamma or epsilon bound.

## Subexponential relative transfer to H_n

Let b_(i,n)=a_3(n,n-i), i=0,1,2, and let D_n=lcm(1,...,n)^5.
The new integer transformation gives the exact signed identities

    b_(i,n)=sum_j c_(i,j) a_3(R_(i,j)).

The already established coefficient recurrence in
`row-balance-and-kappa.md` proves

    log|b_(0,n)|/n -> ell,
    log|b_(1,n)|/n -> ell,
    limsup log(1+|b_(2,n)|)/n <= ell,

where ell=(1/2)log(rho) and rho is the largest root of
z^3-30510z^2+15146217z+729. The polynomial normalizations of the
offset blocks do not change these rates. The first block is nonzero.

Define T_n=||(b_(0,n),b_(1,n),b_(2,n))||_2/|b_(0,n)|.
Then T_n>=1 and log(T_n)/n -> 0. The lower bound uses the first
coordinate. For the upper bound, the numerator has rate ell because
each coordinate has upper rate at most ell and the first has rate ell.
Subtracting the first coordinate's rate proves the limit.

Thus the actual transfer is

    H_n=(D_n/g_n)|b_(0,n)| T_n,
    log H_n/n = 5+ell-log(g_n)/n+o(1).

There is no additional log(6sqrt(3)) rate or branch-maximum rate in
this signed calculation. This improves the loose absolute transfer
envelope obtained by multiplying W_n and P_n. It recovers, rather than
improves, the previously established H upper rate 5.877168; claiming
a smaller H rate still needs additional information about g_n.

## Retaining correlation instead of separating gamma and epsilon

Let a,b be an integral Gauss-reduced kernel basis with Gram entries
A=||a||^2, B=a.b, C=||b||^2, and lambda_1=sqrt(A). Put X_n=||x_n||.
Saturation gives AC-B^2=H_n^2, and

    sqrt(3)/2 <= sin(theta_n)=H_n/sqrt(AC) <= 1,
    kappa_n H_n = H_n^2/[lambda_1^2 sin(theta_n)].

Consequently, with gamma_n=log(Gamma_n)/n and
epsilon_n=log(kappa_n H_n)/n,

    gamma_n-epsilon_n/2
      = [log(Gamma_n*g_n*lambda_1)-log(X_n)]/n
          + log(sin(theta_n))/(2n).

The angular term is uniformly O(1/n). Since log(X_n)/n -> 5+ell,
the exact asymptotic rate of the positive-rounding cost majorant is

    10+ell-liminf log(Gamma_n*g_n*lambda_1)/n.

Here the residual factor has the proved zero logarithmic rate. This
identity retains correlations between the arithmetic content, the
normal gcd, and the shortest relation. It does not subtract separate
upper limits as though they were ordinary limits.

Including the raw analytic decay rate -a_5, with
4.970793860341<a_5<4.970793860358, the sufficient joint target is

    liminf log(Gamma_n*g_n*lambda_1)/n > 10+ell-a_5.

The threshold lies in
(10.183769359549,10.183769359567). Using the proved lower rate

    liminf log(g_n)/n >= c_g
      =3+pi/(4sqrt(3))+(3/4)log(3),

it suffices to establish

    liminf log(Gamma_n*lambda_1)/n > 5.906360302008.

The conservative strict decimal threshold is above the certified upper
endpoint 5.906360302007491. The constants are obtained by rational root
isolation and logarithm intervals, not extrapolated finite family values.
An unbounded eligible subsequence satisfying the strict rate would suffice.

This is the existing joint cost target expressed through the signed H
transfer. It is not an additional independent hypothesis or a proof of
the required joint arithmetic lower bound. It is less restrictive than
prescribing the particular separate constants gamma>5.12 and epsilon<0.24.

## Exact finite verification

`correlated_transfer_budget.py` verifies the algebraic correlation at
all eleven stored indices. Fourth powers avoid numerical square roots.
With J_n^2=Gamma_n^2*g_n^2*A and

    M_n^2=D_n^2*X_n^2/J_n^2,

the fourth power of the core D_n*sqrt(kappa_n H_n)/Gamma_n is exactly
M_n^4*AC/H_n^2, with 1<=AC/H_n^2<=4/3. The script checks these rational
identities and stores rigorous intervals for the correlated rates and
the relative signed transfer. It also isolates rho to eighty bisection
steps and encloses both threshold constants.

No asymptotic lower bound for Gamma_n*lambda_1 is inferred from those
finite records. The current sharp arithmetic growth and distortion
estimates remain unproved; the all-odd irrationality claim is not
established. The numerical constants here do not automatically apply
to the different higher-weight cancellation lattices. No manuscript or
Lean theorem claim is changed in this pass.
