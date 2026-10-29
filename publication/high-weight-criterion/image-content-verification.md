# Surviving image content: verification scope

The new paper argument proves A_n divides Gamma_(s,n) at every fixed
odd weight s>=5, for the specified consecutive blocks. It gives the
lower asymptotic rate c0=pi/(4sqrt(3))+(3/4)log3-1/2. A distinct
rank-one congruence gives P_n^(r-1) A_n dividing the joint augmented
determinantal content, which includes the lower-row minor gcd.

The proof tracks the rational boundary through residue splitting,
distinguishes the small raw kernel at odd indices from the modified
well-poised kernel, and excludes the finite-degree boundary polynomial.
It does not identify lower-row divisors with Gamma. The image divisor
comes from divisibility of both cleared coefficient rows themselves.

The script check_image_content_divisor.py passes eight actual profiles
at weights 7,9,11 and indices 40 through 120, including 315 local
coefficient congruences, both product divisors, and the exact primitive
Cramer ratio after lower-content division. These finite checks support
the separate paper proof and are not used to extrapolate its limits.
An additional 45 direct product-jet checks verify the small raw kernels,
including odd indices, independently of the logarithmic-jet algorithm.

Three new lemmas in KernelProjectorContent formalize preservation of
entry divisors under integer pairings, general finite image contents,
and the integral projection. The actual factorial-family congruence,
prime-number-theorem argument, and asymptotic rate are paper proofs,
not claims of full formalization in Lean.

The changed module and a focused driver compiled successfully. The driver
prints dependencies for dvd_integralPairing_of_entries,
entries_dvd_image_content, and entries_dvd_projectedRowsContent. All three
use only propext, Classical.choice and Quot.sound; the records are in
image-content-axioms.log. A broad driver importing unrelated modules was
interrupted without a result, and its prior source and log were restored.
No fresh full-library rebuild is claimed. The existing manuscript was
edited in place and compiled successfully with the desktop compiler.

The improved explicit relative-cost rate at weight seven is still
approximately 14.995737, exceeding the sharp analytic allowance
0.781973. Thus the negative scalar rate and all-odd irrationality
endpoint remain unproved. The positive lower bound on little gamma
is a new arithmetic conclusion, not completion of that endpoint.
