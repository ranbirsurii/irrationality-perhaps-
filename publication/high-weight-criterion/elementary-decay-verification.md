# Elementary analytic estimates for the weight-seven cubic

The manuscript's proposition Elementary combined-form majorant proves,
for every eligible even n and either constructed primitive form,

  abs(L_(n,i)) <= C_7 (n+1)^16 d_n^7 J_(n,i) 2397^(-n),
  J_(n,i)=sum_(ell=0..3) abs(q_(ell,n,i)) (12n^2)^ell,
  C_7=12*5^14*3^38.

This is a proved all-index paper bound, retaining the primitive cubic
coefficients. Its proof uses a one-variable global maximum, elementary
factorial inequalities, an exact fixed-offset product identity, and
integral comparison for the four positive moments. It does not assume
the desired coefficient-height estimate or irrationality.

The stationary polynomial is

  p(y)=5y^4-2y^3-13y^2-7y-1,
  p(2+z)=5z^4+38z^3+95z^2+77z-3.

The unique saddle lies below 25309/25000. Integer certificates at that
endpoint give the global exponential factor 2397^(-n). Consequently
an upper rate for J_(n,i) strictly below log(2397)-7>0.78 would yield
decay of both primitive forms. That coefficient-height bound is not
proved. The new analytic bound is not a complete irrationality proof.

## Formal verification

`WeightSevenElementaryBounds.lean` contains five proved statements:
the stationary factorization, shifted polynomial identity, positive
endpoint, base-2397 inequality, and moment-cutoff inequality. The module
and updated `VerifyCombinedCubic.lean` compiled with exit code zero.
The latter now checks ten statements including the preceding five cubic
identities. Its axiom records use only propext, Classical.choice, and
Quot.sound. There are no added mathematical axioms or proof placeholders.
The full saddle calculus, factorial estimate, infinite moments, and
application to the Padé kernels remain the manuscript's paper proof.
The complete library entry point also compiled successfully after export
of the new module; unchanged modules were imported from compiled objects.

`scripts/check_weight_seven_elementary_bounds.py` independently verifies
the exact scalar inequalities and log budget, then evaluates the resulting
majorant on the existing primitive pairs. It exceeds one at the smaller
recorded indices, and is below one for both forms at n=40. It is not
extrapolated to an asymptotic assertion. The reproducible data are in
`notes/weight-seven-elementary-bounds.json`.

The existing manuscript source was edited in place and successfully
compiled using the built-in editor. No separate PDF was compiled.

## Further arithmetic route examined

A single short primitive vector could replace control of the second
minimum if its numerical form were proved nonzero. The existing cubics
were tested for a sufficient global sign certificate: all coefficients
after translating u by (n-2)(2n-2) have one sign. The first reduced vector
has this certificate at n=12 and 20, whereas at n=40 it is the second
vector that does. Neither vector has this particular certificate at
n=6 or 8. Mixed signs do not prove that a cubic changes sign; this test
only establishes the stated sufficient certificates when they hold.
No all-index sign theorem for the first minimum was obtained. Thus
Minkowski's short-vector bound alone is not used to assert nonvanishing.
