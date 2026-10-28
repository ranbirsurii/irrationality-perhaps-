# A different construction: double poles, higher derivatives, and Poisson

This attempt uses a different rational kernel, rather than another
estimate for the Gauss-reduced coefficient height. It does not prove
irrationality.

For r>=2, s=2r+1, m>=1, n>=r*m, set

  R(t)=(n!)^2/(m!)^(2r) product_(v=1..m)(t-v)^(2r)
                               / product_(h=0..n)(t+h)^2.

It has only double poles, decays at least quadratically, and has zeros
of order 2r at every positive integer up to m. Its order-(2r-1)
derivative therefore vanishes at those integer zeros. The sum of its
normalized negative derivative is exactly A*zeta(s)+B: all lower periods
are eliminated because the sum of simple-pole coefficients is zero.
The manuscript supplies all Laurent coefficients and the complete
integrality argument, with primitive factor D/g, D=d_n^s.

This construction admits Poisson summation after extending the kernel
by zero to the left of m. The manuscript verifies the regularity and
absolute convergence needed for that application, rather than treating
the piecewise function as a Schwartz function. It obtains

  abs(L_raw) <= V/[12(2r-1)!],
  V=abs(R^(2r)(m))+integral_(m..infinity) abs(R^(2r+1)(t)) dt,

and a fully explicit rational upper bound W for V. The primitive bound
is D*W/[12g(2r-1)!]. A standard Fourier-periodization statement is reviewed
in [Kim's number theory seminar, notes by Andrew Lin](https://web.stanford.edu/~lindrew/18.784.pdf),
pages 37-38; the manuscript separately justifies the regularity for this
specific rational-kernel extension.

`scripts/isolated_derivative_family.py` checks eighteen examples at
weights 5,7,9 and n=12,24,40, with two choices of zero length. It verifies
the partial-fraction identity at three rational points, the residue sum,
the denominator assertions, the exact boundary derivative, and the
primitive Poisson majorant against independent Euler--Maclaurin intervals.
All eighteen primitive-form intervals are outside [-1,1]. Thirteen are
positive and five negative. This is not extrapolated to an all-index
sign or asymptotic impossibility statement.

The new family does remove the lower-period cancellation lattice.
The remaining requirements are a negative rate for its fully primitive
form and arbitrarily late nonvanishing. Neither is proved. The metric
and parameter constructions in the earlier sections are defined at
every eligible index, but that fact does not supply these estimates.

## Exact transition to the original decay family

At common even indices n>=max(2r,r*m), let (a,b) be this family's
primitive integer coefficient pair. If M is the original full cleared
Pade matrix, delta=det(M), and z=(0,...,0,a,b), then

  v=adj(M)z/delta, Mv=z,
  a*zeta(s)+b=d_n^s sum_j v_j A_(s,n,n-j).

Let t be the least coordinate denominator of v and w=t*v. Then w is
integral and its coefficient gcd is exactly t. This supplies the exact
transition back into the original family, with primitive normalization
preserved. The old decay estimates can therefore be applied to this
form with the actual norm/weighted height of v. That transition factor
has no proved favorable exponential rate.

`scripts/check_cross_family_transition.py` verifies all eighteen stored
primitive coefficient pairs, integer lifts, exact gcds, and transferred
profile bounds. Every transferred majorant is above one at these indices.
The all-index matrix identity is a paper proof; the finite checks do not
replace a uniform estimate for the transition cost.
