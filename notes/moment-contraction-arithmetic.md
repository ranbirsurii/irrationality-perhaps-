# Adjacent ratios and arithmetic input

Let R_(s,n)=d_n^(2s) mu_(s,n) nu_(s,n). All quantities are the complete
moment-metric bounds, with nu the second reduced binary coefficient.
The exact ratio is

    R_(s,n+2)/R_(s,n)
      = (d_(n+2)/d_n)^(2s) (mu_(s,n+2)/mu_(s,n))
                              (nu_(s,n+2)/nu_(s,n)).

If this ratio is eventually at most q_s<1, induction proves geometric
decay along the even indices. No polynomial majorant or squeeze argument
is needed for that implication. The ratio inequality remains unproved.

The adjacent lcm quotient is explicit: d_N/d_(N-1) is p when N is a
power of a prime p, and one otherwise. Thus its logarithm over two steps
is the sum of log(p) for prime powers in (n,n+2]. This identity includes
all prime powers, not only primes. It gives the denominator contribution
exactly, but no bound for the changing reduced coefficient nu.

The script `moment_adjacent_ratios.py` checks eight adjacent ratios at
each weight 7,9,11, starting at its first eligible index. All 24 exact
ratios are below 1/100000. The comparison uses fractions, not rounded
decimals. The worst tested ratio is at weight 7, step 16 to 18; small
ratios at nearby indices do not certify a uniform contraction.

## Applicable literature and the missing identification

[Zudilin, Arithmetic of linear forms involving odd zeta values](https://arxiv.org/pdf/math/0206176)
develops arithmetic normalization of hypergeometric forms. Its Section 5
uses a prime-product arithmetic saving in its specific family, and
Section 8 treats higher odd-zeta forms. Such savings require the actual
factorial data and valuation inequalities; their exponents cannot be
assigned to the inverse-matrix reduced moment coefficient nu without
an additional argument.

[Fischler, Linear independence of odd zeta values using Siegel's lemma](https://arxiv.org/abs/2109.10136)
constructs forms using Siegel's lemma and applies multiplicity estimates
to a period system. It does not state an adjacent contraction for the
isolated-target metric in this repository. Importing its conclusion
would not prove that contraction.

The applicable research route is therefore to derive factorial/minor
valuation bounds for this family and an archimedean comparison for the
reduced quadratic forms. Prime distribution estimates alone control
neither the divisibility of those minors nor the short-vector change.
No theorem establishing the necessary comparison was identified in
these sources. This is a precise applicability assessment, not a proof
that a suitable contraction is impossible.

## Factoring a common divisor exactly

Suppose a nonzero scalar h is removed from the whole cleared coefficient
matrix and its clearing multiplier: M'=M/h, D'=D/h. Then F'=hF,
S'=h^2 S. The same reduced unimodular witness reduces S', with
nu'=h^2 nu. Consequently

    (D')^2 mu nu'=(D/h)^2 mu h^2 nu=D^2 mu nu.

Thus identifying such a common factor via Frobenius or a Galois
representation does not alone improve this complete bound. A useful
arithmetic improvement needs additional relative divisibility or a
comparison of the actual reduced metrics, with the realization of this
specific matrix proved. No representation realizing those additional
properties is constructed here. `moment_cost_common_factor_invariant`
formalizes the scalar identity, without assuming any Galois realization.

## Checked statements

`MomentMajorant.lean` verifies the homogeneous reduced quadratic bound,
the limit of a shifted real polynomial times a decaying exponential,
and the eventual-majorant implication. The module compiles. Its
verification driver records dependencies. It assumes the majorant
inequality as an explicit argument and proves no such inequality for
the actual family. The expanded moment arguments are included in the
existing manuscript, whose current source compiles in the editor.
