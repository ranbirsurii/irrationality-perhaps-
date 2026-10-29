# Take the minimum through moving integer points

Fix the actual rational binary metric Q_n, with entries A,B,C and
h=(AC-B^2)/A>0, theta=B/A. Work at the actual moving slope theta_n,
not just its limit 1/zeta(s). The Schur identity is

    Q_n(u,v)=A*(u+theta*v)^2+h*v^2.

## Construct the variable points

Compute exact continued fractions of the rational theta. Adjacent
convergents p/q and p'/q' give integer points

    y=(-p,q), y'=(-p',q'), det(y,y')=+1 or -1.

Put V=max(q,q')=q', except for the initial denominator-zero convention.
The usual recurrence and determinant identity give

    |theta*q-p|<=1/V, |theta*q'-p'|<=1/V.

For example the exact complete-tail expression for the earlier error
has denominator q'+tau*q with tau>=0; the next error is no larger.
For a terminal rational convergent the final error is zero. The initial
pair (1,0),(floor(theta),1) also satisfies the displayed inequalities.
The points are therefore independent integer coefficient pairs, including
the rational terminal case. No nonvanishing assumption about one form
is required.

For both points the exact quadratic bound is

    Q_n(y),Q_n(y')<=A/V^2+h*V^2.

Binary minimum optimality now supplies a direct cost bound

    R_n=mu_n*nu_n<=mu_n*(A_n/V_n^2+h_n*V_n^2).       (1)

This is an alternative to lower-bounding alpha_n: construct a short
independent pair and upper-bound the second minimum directly.

## Balance the two terms

Let H=(A/h)^(1/4), lambda=V/H. Then the right side of (1) is exactly

    mu*sqrt(det Q)*(lambda^2+lambda^(-2)).           (2)

As the convergent denominators increase, A/V^2+h*V^2 decreases until
V reaches H, then increases. It is enough to retain the last available
denominator below H and the first above H, and select the smaller
envelope. If the rational continued fraction ends first, retain its
terminal pair. This is a fully specified moving-point construction.

For the stronger adaptive tail tolerance delta_n=16^(-n) derived in
ideal-schur-growing-range.md,

    det(mu_n*Q_n)<=400*16^(-n),
    mu_n*sqrt(det Q_n)<=20*4^(-n).

Consequently the complete bound becomes

    R_n<=20*4^(-n)*(lambda_n^2+lambda_n^(-2)).        (3)

Thus a sufficient all-index epsilon target for these explicit points is

    limsup log(lambda_n^2+lambda_n^(-2))/n < log 4.  (4)

For instance a proved bound lambda_n^2+lambda_n^(-2)<=exp(n) eventually
would imply a strictly negative upper rate at most -(log 4-1). More
generally any rate strictly below log 4 leaves the required epsilon.
The construction does not require a bounded distortion factor.

The uniform estimate (4) for the actual moving convergents is NOT proved.
Choosing a denominator near H is a concrete algorithm; the size of its
overshoot or undershoot requires an arithmetic theorem. No generic
continued-fraction theorem is asserted to supply that rate automatically.

## Exact and formal checks

variable_point_minimum.py uses the forty stored fixed-cutoff rational
metrics. It verifies determinant +-1, both error inequalities, both full
quadratic values, and the upper bound (1). The bound/optimum ratio is
at most 2.073 in these finite tests. It stores the exact balance ratio
(V/H)^4, avoiding floating-point comparisons in the selection.
These records are not the stronger adaptive sequence used in (3),
and they are not extrapolated to an asymptotic balance bound.

Lean checks the variable-point quadratic bound and the exact balance
identity. The existing independent-pair minimum theorem provides the
minimization step. Continued-fraction selection and its family-specific
asymptotic application remain paper arguments. The negative normalized
rate and the all-odd irrationality theorem remain unproved.
