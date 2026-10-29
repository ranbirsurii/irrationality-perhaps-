# Exact ideal bridge and uniform asymptotics on the growing range

Fix an odd s>=7 and write z=zeta(s). The coefficient Gram matrix Q_n
is 2 by 2; n is its sequence index. The scalar mu_n is kernel mass,
not a successive minimum. Alpha_n is the intrinsic first squared minimum.

## Algebraic lattice routes

Under U in GL_2(Z), Q changes to U^T Q U. Its determinant and the set of
values on nonzero integer vectors are unchanged. Consequently its first
minimum is unchanged. Binary Gauss reduction already attains the second
minimum and the proved 4/3 comparison. A new coordinate basis alone
does not improve the intrinsic ratio mu*det(Q)/alpha. An explicit short
basis could prove a family bound, but that bound must concern the same
intrinsic minima. This corrects the earlier loose wording about increasing
alpha by choosing a basis.

There is an actual quadratic-ideal representation. Write

    Q=eta*[[a,b/2],[b/2,c]], gcd(a,b,c)=1, eta>0,
    Delta=4ac-b^2>0, beta=(b+sqrt(-Delta))/2.

The order Z[beta] is closed because beta^2-b*beta+ac=0. Its subgroup
I=(a,beta) is an ideal: multiplication by beta preserves both generators.
For integers x,y,

    Norm(a*x+beta*y)=a*(a*x^2+b*x*y+c*y^2).

Thus alpha=eta*m, where m is the least positive represented integer,
and det(Q)=eta^2*Delta/4. If N_min is the least nonzero element norm in I,

    C=mu*eta*Delta/(4m)=mu*eta*a*Delta/(4*N_min).

This supplies the requested ideal identification. The elementary norm
bound N_min>=a gives only m>=1, exactly the existing content bound.
It does not supply the exponential gain. No controlled field discriminant,
conductor or ideal-class estimate giving a larger N_min is assumed.

## Analytic choice: Schur complement

Write Q_n=[[A_n,B_n],[B_n,C_n^entry]], and set

    theta_n=B_n/A_n, h_n=det(Q_n)/A_n,
    r=99/100, epsilon=-log r>1/100,
    T_n=mu_n*det(Q_n)*r^(-n).

Completing the square gives the exact identity

    Q_n(u,v)=A_n*(u+theta_n*v)^2+h_n*v^2.

Hence alpha_n>=T_n is equivalent to A_n>=T_n and the finite tests

    ||theta_n*v||_Z^2 >= sigma_n^2*(V_n^2-v^2),
    1<=|v|<V_n,
    sigma_n^2=det(Q_n)/A_n^2, V_n^2=mu_n*A_n*r^(-n).   (1)

For v=0 the minimum is A_n. Outside this range the second square term
already exceeds T_n. For each remaining v the closest integer u gives
the exact test. If (1) holds at all sufficiently large indices, then
R_n<=(4/3)r^n, proving the desired epsilon shift. This implication does
not assert the uniform tests have been proved.

## The full growing-range asymptotic

Strengthen the adaptive rule to delta_n=16^(-n), using the coefficient
basis (1,0),(0,1): require tau_0/P<=delta_n and
mu*max(H_11,H_22)<=delta_n^2. The fixed-index tail convergence proves
termination, just as before. All these checks are rational. The resulting
prefix row q=(q_1,q_2) satisfies

    |q_1-z|<=delta_n, |q_2-1|<=delta_n,
    1<=mu/P<=1+delta_n, |mu*H_12|<=delta_n^2.

The last bound follows from positive semidefiniteness of H. Put
a_n=mu*A_n, b_n=mu*B_n, c_n=mu*C_n^entry. Since 1<z<2,
direct expansion of mu*Q=(mu/P)*q*q^T+mu*H gives

    z^2<=a_n<=z^2+15*delta_n,
    |b_n-z|<=11*delta_n, 1<=c_n<=1+8*delta_n,
    0<det(mu*Q_n)<=400*delta_n.

Consequently the precise range and slope asymptotics are

    V_n=z*(100/99)^(n/2)*(1+O_s(16^(-n))),
    theta_n=1/z+O_s(16^(-n)),
    0<sigma_n^2<=400*16^(-n).                         (2)

These are uniform analytic estimates for the entire growing range, not
fixed-v limits. In particular distance to the integers is 1-Lipschitz,
so simultaneously for every integer 1<=|v|<V_n,

    abs(||theta_n*v||_Z-||v/z||_Z)
      <=37*delta_n*V_n
      =O_s((sqrt(100/99)/16)^n).                      (3)

The right side of the required inequality (1) is uniformly at most

    400*19*((100/99)/16)^n.                          (4)

The constants 37 and 400 are conservative explicit bounds from the
displayed entry estimates. Since a_n>=z^2>=1,
|theta_n-1/z|<=|z*b_n-a_n|/(z*a_n)<=37*delta_n and
sigma_n^2=det(mu*Q_n)/a_n^2<=400*delta_n.

Define the full-range minimum

    M_n(x)=min_(1<=v<V_n) ||v*x||_Z.

The same finite range is used for both slopes. Equation (3) proves

    M_n(theta_n)=M_n(1/z)
                  +O_s((sqrt(100/99)/16)^n).         (5)

This is the obtained asymptotic for the full growing-range problem.
It does not determine the arithmetic minimum M_n(1/z). A uniform lower
bound on that minimum strong enough to dominate (4) remains unproved.
In particular analyticity and small slope error cannot rule out an
exact rational resonance of 1/z without additional arithmetic input.
No negative common normalized rate or irrationality is concluded here.

## Checks

The exact script verifies the norm and scalar-ratio identities and the
finite tests (1) on forty stored cases. Each uses at most two positive
v-values at these finite indices. This does not bound the number of
slices as n grows; (2) shows that number grows exponentially.

Lean checks determinant pullback, unimodular nonzero vectors and lower-
bound invariance, the norm identity, scaled Gram determinant, integer
value floor, Schur completion, large- and small-coordinate bounds, and
uniform slope perturbation. The ideal-order interpretation and actual
family asymptotics above are paper derivations, not claims of a full
Lean formalization of the ideal or the zeta arithmetic lower bound.
