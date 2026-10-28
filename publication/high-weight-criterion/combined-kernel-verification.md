# Direct weight-seven combined kernels

This continuation implements the three proposed tasks as far as the
proof permits. It does not establish a new irrationality theorem.

The manuscript section Direct combined-kernel construction at weight
seven supplies an exact algorithm at every even n>=6: invert the full
augmented matrix using adjugate columns, Gauss-reduce their integral Gram
form, and lift each resulting rational vector to an integer vector. The
coefficient gcd of that lift is exactly its least coordinate denominator.
The two primitive coefficient pairs have determinant plus or minus one,
so at least one form is nonzero for every eligible index.

Each combined rational kernel is the common block T_(7,n,n-3) times a
nonzero cubic in u=t(t+n), with every coefficient specified. This preserves
cancellation before taking absolute values. A proved all-index tail
estimate at K=n^2 gives

  R_(n,i)(n^2) <= 432 n^6 D_n norm(v_i)_1 4^n n^(-3n),

and log(norm(v_i)_1)=O(n) follows from the already proved elementary
cost envelope. Thus the absolute tail tends to zero with logarithmic
rate at most -3 relative to n log n. This does not require the missing
sharp arithmetic growth bound.

The remaining task is convergence to zero of the explicitly displayed
finite signed sum from n-2 to n^2-1. No proof of that assertion has been
obtained. In particular the three-step proposal is not fully completed.

## Formal scope

`CombinedKernelCubic.lean` compiled with exit code zero and contains five
proved identities: the cubic expansion, paired quadratic factor,
reflection, triangular coefficient injectivity, and absolute majorant.
`VerifyCombinedCubic.lean` also compiled with exit code zero. Its dependency
records in `combined-cubic-axioms.log` use only propext, Classical.choice,
and Quot.sound. There are no added mathematical axioms or placeholders.
The actual factorial-kernel identification, all-index matrix rank,
primitive-pair construction, and tail convergence are paper arguments;
they are not asserted as complete Lean theorems by these five lemmas.

## Exact independent checks

`scripts/weight_seven_combined_kernel.py` constructs both forms at indices
6, 8, 12, 20, and 40. At each index it verifies integer cancellation,
the exact coefficient gcd, the unimodular target pairs, the cubic product
identity, and a rational interval computed from the joint kernel with
its rigorous infinite-tail bound. All ten intervals exclude zero and
are contained in (-1,1). Independently computed Euler--Maclaurin intervals
for p*zeta(7)+q are contained in the joint-kernel intervals. The records
are in `notes/weight-seven-combined-kernel.json`.

These finite checks verify the computation; they are not extrapolated.
The direct method uses product identities and a monotonicity estimate.
No harmonic or Poisson estimate is assumed for the unresolved finite sum.
The existing manuscript was edited in place and compiled successfully
with the built-in document compiler. No replacement PDF was compiled.
