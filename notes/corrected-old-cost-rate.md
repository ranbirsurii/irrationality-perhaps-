# Rate calculation for the proposed weight-five cost bound

Retain the repository's definition d_n=lcm(1,...,n). Then
log(d_n)=psi(n)=n+o(n), by the prime number theorem. The identity follows
by summing log p once for each prime power p^k<=n. The asymptotic is
recorded in [NIST DLMF 25.16.3](https://dlmf.nist.gov/25.16.E3).

Consider the older weight-five upper bound in the supplied message:

  K_n <= (3*d_n^5*(1+2R_n)/Gamma_n)
           sqrt(2*kappa_n*||x_n/g_n||_2/sqrt(3)).

Here R_n in (1+2R_n) is the older residual factor, not the complete
moment cost called R_n in the current construction. Suppose the
quantities are positive, log(1+2R_n)=o(n),
liminf log(Gamma_n)/n>=gamma, and
limsup log(kappa_n*||x_n/g_n||_2)/n<=epsilon. Then the valid estimate is

  limsup log(K_n)/n <= 5-gamma+epsilon/2.

The contribution 5 cannot be replaced by zero: the lcm is exponential,
not polynomial. Thus the stated assumptions gamma>=0.06 and epsilon<0.12
do not force this bound negative. A sufficient condition for K itself
to decay is gamma>5+epsilon/2.

The proposed epsilon/2-gamma budget is valid if gamma is instead a
lower rate of the relative saving Gamma_n/d_n^5. An eventual bound
Gamma_n>=d_n^5*exp(gamma*n) would supply that interpretation; the
weaker Gamma_n>=exp(gamma*n) does not. No such stronger relative
saving is proved here.

One need not demand decay of K alone if it multiplies an analytic form
with rate at most -a. The complete product then has upper rate

  5-a-gamma+epsilon/2.

For the previously computed weight-five raw rate a approximately
4.97079386035, this requires gamma>0.02920613965+epsilon/2.
At gamma=0.06 a sufficient strict distortion bound is epsilon below
approximately 0.06158772070, rather than merely below 0.12.
These numerical thresholds explain the budget; they are not proofs of
the required Gamma or distortion estimates for the actual family.

In the current moment construction the explicit clearing multiplier
has already canceled exactly: d_n^(2s)*mu_n*nu_n=mu_n*nu_raw,n.
No additional lcm condition is appended to that formulation. The
weight-five expression above cannot establish the all-weight moment
limit by dropping a factor, changing notation, or assuming the stated
Gamma and geometric rates. Those family-specific rate bounds remain
unproved here. The unconditional all-odd conclusion is not established.

The subsequent assertion gamma>5.12 and epsilon<0.24 would meet the
strict numerical threshold if proved for the relevant family. The
supplied text states these values without a contour identity for the
arithmetic gcd Gamma_n or a proved lower growth bound for that gcd.
The explicit contour derived in this pass evaluates the actual raw
moment determinant, not Gamma_n. The Euler gamma functions appearing
in that contour are different objects from the arithmetic gcd Gamma_n.
No such lower growth estimate is inferred from their shared name.
Even after a negative limsup bound -delta is proved, an eventual bound
with exponent -delta/2 is safe; an exponent exactly -delta need not
follow without a stronger margin.
