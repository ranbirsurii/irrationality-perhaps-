# Adjugate signed-prefix certificate

The construction keeps the signed block combination inside a single
polynomial H_n(t(t+n)) and then keeps its finite sum signed. Only the
infinite tail is bounded using absolute coefficients. The factorial
normalization is already inside H_n, so D and Gamma are not charged
again.

The paper proves an explicit rational tail bound e_K, convergence
e_K->0 at each fixed index and pair, and the two-sided certificate

    |p zeta(s)+q| <= R_K <= |p zeta(s)+q|+2 e_K.

A doubling cutoff with e_K<=4^(-n) therefore introduces no fixed
positive majorant floor. It changes evaluation precision, not the
integer coefficients. This applies the previous signed-prefix method
to the adjugate-root construction rather than changing the family.

The exact script passes eight certificates at weights 7 and 9, checks
24 pointwise combined-kernel identities, and compares all intervals
with independent Euler-Maclaurin zeta enclosures. The fixed pair (-1,1)
gives the nonzero constant 1-zeta(s). The selected unmodified cofactor
roots give large forms in these examples. These choices are not a
proved decaying sequence.

The new Lean theorem signed_prefix_certificate_sharp verifies the
two-sided error-to-majorant implication. The factorial tail application
and the all-index cutoff existence above are paper proofs. No uniform
decaying pair selection, all-index nonvanishing or all-odd irrationality
conclusion is claimed.

The changed module and its verification driver compiled successfully.
The driver records 28 theorem dependency reports; the new sharpness
theorem uses only propext, Classical.choice and Quot.sound, with no
sorryAx. The existing manuscript compiled successfully after the
certificate derivation was added in place. No full-library rebuild
is claimed.
