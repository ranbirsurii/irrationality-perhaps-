# Global adjacent-coefficient signs at weight five

For every even n>=2 the normalized weight-five coefficients satisfy

\[
 \boxed{(-1)^{n/2}\alpha_{n,n}>0,\qquad
        (-1)^{n/2+1}\alpha_{n,n-1}>0.}
\]

In particular alpha_(n,n)*alpha_(n,n-1)<0 at every even index n>=2.
The proof below uses two exact creative-telescoping certificates and a
positivity-preserving recurrence cone. It is not an extrapolation from
the finite sign checks. The integer-polynomial verifier uses only the
Python standard library. Lean verifies the positivity induction and the
coefficient inequalities. The interpretation of the certificates as
recurrences for the actual Laurent-coefficient sums is proved on paper
below, not yet formalized inside Lean.

## Definitions and certificate format

For a=0,1 set

\[
 R_n^{(a)}(t)=(n!)^3
 \frac{\prod_{v=1}^{n-a}(t-v)(t+n+v)}{\prod_{j=0}^{n}(t+j)^5},
 \qquad n\ge2.
\]

Let v_n^(a) be the sum of its third-order partial-fraction coefficients.
The original normalized coefficients obey

\[
 \alpha_{n,n}=v_n^{(0)},\qquad
 \alpha_{n,n-1}=n^2v_n^{(1)}.
\]

For each a, `pade-sign-recurrence-a.json` specifies integer coefficient
lists in ascending powers of n for four polynomials q_0,...,q_3, four
polynomials P_0,...,P_3, and 31 polynomials x_0,...,x_30. Set

\[
 X(n,t)=\sum_{k=0}^{30}x_k(n)t^k,\quad
 U=t^6(t+2n-a+1),\quad V=(t-n+a-1)(t+n+6)^6,
\]

\[
 H_\ell(n,t)=
  \prod_{i=1}^{2\ell}(t-n+a-i)
  \prod_{i=1}^{4\ell}(t+2n-a+i)
  \prod_{i=2\ell+1}^{6}(t+n+i)^6.
\]

The certificate is the integer-polynomial identity

\[
 \boxed{U(n,t)X(n,t+1)-V(n,t)X(n,t)
                  =\sum_{\ell=0}^3q_\ell(n)H_\ell(n,t).}
 \tag{1}
\]

The verifier expands both sides in Z[n,t] and checks every coefficient
exactly. Thus (1) holds at all n,t. No sampling or floating-point
arithmetic is used to verify it. It also verifies

\[
 q_\ell(n)\prod_{i=2\ell+1}^{6}(n+i)^3=g_a(n)P_\ell(n),
\]

where

\[
 g_0(n)=\prod_{i=3}^{6}(n+i)^3,
 \qquad g_1(n)=\prod_{i=2}^{6}(n+i)^3.
\]

These factors are strictly positive for n>=2. The P polynomials all have
degree 25 for a=0 and degree 36 for a=1. The files give their complete
coefficients, so the theorem specifies finite explicit recurrences.

## From the certificate to the coefficient recurrence

Put D(n,t)=product_(i=1..6)(t+n+i)^6 and B(n,t)=R_n^(a)(t)/D(n,t).
Cancellation of the displayed products gives

\[
 \frac{B(n,t+1)}{B(n,t)}
  =\frac{t^6(t+2n-a+1)}{(t-n+a)(t+n+7)^6},\qquad
 B(n,t)H_\ell(n,t)
  =\frac{R_{n+2\ell}^{(a)}(t)}{\prod_{i=1}^{2\ell}(n+i)^3}.
\]

Use these as rational-function identities, or after multiplying by their
denominators, so zeros cause no ambiguity. Define

\[
 G(n,t)=V(n,t)X(n,t)B(n,t).
\]

Multiplying (1) by B(n,t) yields

\[
 G(n,t+1)-G(n,t)
  =\sum_{\ell=0}^3\frac{q_\ell(n)}{\prod_{i=1}^{2\ell}(n+i)^3}
                           R_{n+2\ell}^{(a)}(t).
\]

Apply the functional that sums all third-order partial-fraction
coefficients in the integer pole orbit. Shifting t by one does not
change that sum: it only shifts each pole by one. Therefore the
functional vanishes on G(t+1)-G(t). G has only finitely many integer
poles, so this argument is a finite cancellation, not an interchange
of infinite sums. It gives, after clearing the positive factors,

\[
 \boxed{\sum_{\ell=0}^3P_\ell(n)v_{n+2\ell}^{(a)}=0.}
 \tag{2}
\]

No linear independence of 1,zeta(3),zeta(5) is assumed: the functional
is applied to a rational-function identity before evaluating any period.

## A uniform positivity cone

For both certificates, the coefficient lists of

\[
 -P_0(x+2),\quad P_1(x+2),\quad P_2(x+2),\quad P_3(x+2),
\]

and of

\[
 10^6P_2(x+2)-10^9P_3(x+2)-1000P_1(x+2)+P_0(x+2)
\]

are nonnegative integers, with strictly positive constant terms.
The verifier checks these polynomial identities coefficient by coefficient.
They prove inequalities for every real x>=0. In particular, at n>=2,
put A=-P_0(n)>0, B=P_1(n)>0, C=P_2(n)>0, D=P_3(n)>0. Then

\[
 10^6 C>10^9D+1000B+A.
 \tag{3}
\]

Let u_k^(a)=(-1)^(k+1+a)*v_(2k+2)^(a). Equation (2) becomes

\[
 D u_{k+3}=C u_{k+2}-B u_{k+1}-A u_k.
\]

Suppose u_k>0, u_(k+1)>=1000*u_k and u_(k+2)>=1000*u_(k+1).
Then u_k<=u_(k+2)/10^6 and u_(k+1)<=u_(k+2)/1000. Hence (3) gives

\[
 D u_{k+3}
 \ge\left(C-\frac B{1000}-\frac A{10^6}\right)u_{k+2}
 \ge1000D u_{k+2}.
\]

The cone is preserved, so positivity and the successive-ratio lower
bound hold at every k once the first triple satisfies the cone.
The initial triples, obtained from the exact harmonic-binomial coefficient
formula, are

\[
 (u_0^{(0)},u_1^{(0)},u_2^{(0)})
   =\left(882,\frac{9149875}{2},\frac{225341478859}{5}\right),
\]

\[
 (u_0^{(1)},u_1^{(1)},u_2^{(1)})
   =\left(\frac{785}{8},\frac{16148335}{128},\frac{89419424171}{162}\right).
\]

Each first entry is positive and each successive entry is at least
1000 times its predecessor. These are exact rational comparisons.
Induction proves u_k^(0)>0 and u_k^(1)>0 for every k>=0, establishing
the asserted global signs.

## Consequence for nonvanishing, and the remaining arithmetic problem

The two weights alpha_(n,n-1) and -alpha_(n,n) have the same sign for
every even n>=2. The individual normalized kernel sums are strictly
positive. Therefore

\[
 (-1)^{n/2+1}\left[
 \alpha_{n,n-1}\mathcal A_{n,n}-\alpha_{n,n}\mathcal A_{n,n-1}
 \right]>0
\]

at every such n. The zeta(3) coefficient cancels exactly, so these are
nonzero evaluated forms in Q+Q*zeta(5) at arbitrarily large indices.
Nonzero zeta(5) coefficients at every index are not separately asserted.
Clearing denominators and removing a positive full gcd preserves
nonvanishing whenever applied to their nonzero coefficient pair.

This closes the mathematical sign and nonvanishing step for this
specific two-block weight-five family. It does not establish the
winning primitive arithmetic estimate. That still requires a bound on

\[
 K_n=\frac{d_n^5\sum_j|w_{n,j}|}{h_n}
\]

relative to the analytic decay rate. Here w_(n,j) are integer weights
obtained by clearing the two rational cancellation weights, and h_n is
the full coefficient gcd.
The claimed rates 4.85 or 4.91 are not proved by the recurrence argument.
No irrationality theorem for zeta(5), or for all odd zeta values, is claimed.

## Formalization and reproduction

`OddZeta/PadeSignRecurrence.lean` proves the generic cone induction,
the actual polynomial inequalities from nonnegative coefficient lists,
and unconditional positivity of the two explicitly defined recurrence
states with the stated initial triples. The identification of those
states with the actual Laurent-coefficient sequences uses the paper
argument from (1) to (2); that connection is not yet formalized in Lean.
Thus the Lean file is not presented as a complete formalization of the
global Laurent-coefficient sign theorem.

Verify the mathematical certificates with Python 3.11 or newer and its
standard library:

```text
python scripts/verify_sign_recurrences.py
```

The optional discovery script uses SymPy 1.14.0 and takes several minutes
per offset. SymPy is not needed by the independent certificate verifier:

```text
python scripts/generate_sign_recurrences.py --offset 0
python scripts/generate_sign_recurrences.py --offset 1
```

Rebuild the Lean checks with the pinned toolchain:

```text
lake build
lake env lean scripts/AuditSignRecurrence.lean
```

Both optional discovery runs were completed and reproduced the published
certificate objects exactly. The eight new foundation reports use only
standard Lean foundations; they are in `lean-sign-recurrence-verification.txt`.
The complete project entry point compiled after the final import.
The three-page derivation `global-sign-note.pdf` and its TeX source are
included. Both the desktop compiler and Tectonic succeeded, all three
final rendered pages were inspected, and the log has no overfull or
underfull box warnings.
