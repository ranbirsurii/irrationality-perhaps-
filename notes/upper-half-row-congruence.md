# Upper-half primes: a uniform fifth-order row congruence

The complete paper proof is in
`publication/high-weight-criterion/upper-half-row-congruence.tex`, included
by the existing manuscript. Its assumptions are: weight seven, even n,
prime p>7, p<n<2p, and p<=m<=n. No character-distribution assumption is used.

Writing H2=sum_(h=1..p-1) h^(-2), it proves in the p-local rationals

    98 p^6 b + 153 p^3 a3 = 0 mod p^2,

    174 p^7 b + (191+87 p^2 H2) p^4 a3 + 247 p^2 a5 = 0 mod p^5.

The first identity explains all of the handoff's c_p values: they are
the residues of the fixed rational number -153/98. Its source is the
coarse kernel W7=(2X+1)(X-1)(X+2)/(X^7(X+1)^7), with (a3,b)=(-196,306).

For the stronger identity, fourth-order Taylor expansion of the p-adic
unit factors leaves a polynomial of degree at most four. Exact reflection
restricts it to the span of W7 and W6=X(X+1)W7. The two coarse rows
(a3,a5,b) are (-196,-64,306) and (66,18,-98). Both satisfy
174 b+191 a3+247 a5=0. The harmonic boundary is retained explicitly:
it contributes -(p^2 H2/2) times the scaled a3 row. This yields the
coefficient 191+87 p^2 H2 above.

The determinant of the two lower coarse rows is 696=24*29. The integer
174=6*29 in the row identity explains the special denominator prime 29.
For p!=29 and n/2<p<=n-3, pairing with any integer cancellation vector
proves p^5 divides both its target and constant coefficients. Thus

    p^5 | Gamma_(7,n).

There is no loss from lower-row Smith factors: this argument acts directly
on every vector of the saturated integer kernel. At p=29 the same
identity gives the weaker p^4 divisibility. The case (n,p)=(32,29) has
exact content valuation four, so simply omitting that exception from
the fifth-power theorem would be false.

Combining with the earlier first-order product A_n, without counting
its upper-half primes twice, proves

    liminf log Gamma_(7,n)/n >= 2.777409057559...

along even n. Specifically A_n Q_n^4 divides Gamma, where Q_n is the
eligible upper-half prime product excluding 29 and log Q_n/n -> 1/2.

## Attempt at the full theorem

The new factor improves the existing elementary primitive-cost exponent
by two, from 14.995736480048... to 12.995736480048.... This upper bound
uses the natural lower-row two-minor content: at the upper-half primes
it has valuation at least two, so the joint divisor improves from
P_n^2 A_n to P_n^2 A_n Q_n^4. The Smith factor is not counted twice.
The resulting upper bound
still does not imply decay. The signed moment construction avoids some
of that crude growth, but an unbounded-index estimate for its second
integer minimum remains unproved. Neither irrationality of zeta(7) nor
the all-odd irrationality theorem is claimed here.

## Formal and computational scope

`OddZeta/PadicRowTransfer.lean` compiles the exact one-row and two-row
divisibility transfers, including cancellation of scaling powers and a
Bezout unit coefficient. It also verifies the coarse row relation.
It does not yet formalize the local rational-function or harmonic proof.

The script `scripts/audit_upper_half_row_proportionality.py` reconstructs
the actual Laurent rows using rational arithmetic. Its finite tests
supplement the paper proof; they do not replace it. The separately
mentioned user audit files were not located in the accessible project,
Downloads, or attachments, so this audit was reconstructed from the
existing coefficient implementation instead.
