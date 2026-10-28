# Individual primitive normalization of the signed pair

Fix one weight s=2r+1 and an eligible index. Let a,b be an integral basis
of the kernel of the lower-period matrix. Assume that

  delta = Y(a) Z(b) - Y(b) Z(a) != 0.

This assumption follows from full augmented rank by the Smith identity.
The subsequent proof in `augmented-rank-discrete-residue-proof.md` supplies
it, on paper, for every actual consecutive-block profile with even n>=2r.

Set h_a=gcd(Y(a),Z(a)) and h_b=gcd(Y(b),Z(b)). Neither can be zero,
because that would make one column of the coefficient determinant zero.
The individually divided forms have integer coefficients:

  L_a = (Y(a) zeta(s) + Z(a))/h_a,
  L_b = (Y(b) zeta(s) + Z(b))/h_b.

Their coefficient determinant is delta/(h_a h_b), which is nonzero.
Consequently at least one form is nonzero, with no positivity requirement.
This argument does not assume irrationality of the target.

Write A=norm(a)^2, B=a dot b, C=norm(b)^2. With D=d_n^s, N=r+1,
and S the maximum raw form, the cleared period identity and the signed
triangle inequality give

  abs(L_a) <= sqrt(N) D S sqrt(A)/h_a,
  abs(L_b) <= sqrt(N) D S sqrt(C)/h_b.

The Gram matrix of the scaled vectors a/h_a,b/h_b is

  Gsharp = [[A/h_a^2, B/(h_a h_b)], [B/(h_a h_b), C/h_b^2]].

It is positive semidefinite because B^2<=AC. Let mu_sharp denote its
larger eigenvalue, given by the ordinary two-by-two quadratic root formula.
Then

  max(A/h_a^2,C/h_b^2) <= mu_sharp <= tau_sharp,
  tau_sharp = A/h_a^2 + C/h_b^2,
  max(abs(L_a),abs(L_b)) <= sqrt(N) D S sqrt(mu_sharp).

The existing common content Gamma divides both h_a and h_b. Therefore

  tau_sharp <= (A+C)/Gamma^2.

This permits genuine additional savings from each selected vector's own
content. No Gauss reduction hypothesis is imposed after unequal scaling.
In particular, the old reduced-basis inequalities cannot simply be reused
for Gsharp. Nor does this argument assert the generally invalid Loewner
comparison Gsharp <= G/Gamma^2. The displayed scalar trace comparison is
enough for the stated bound.

The new Lean module `OddZeta/PrimitivePairNormalization.lean` proves the
two-by-two positive-semidefinite eigenvalue bounds, their individual
scaling, the common-content trace comparison, the resulting form bounds,
exact casting of the divided integer forms, and determinant-based
nonvanishing. The actual integral basis, coefficient identification,
and asymptotic estimates remain mathematical inputs to its application.

## The remaining quantitative task

The proved raw analytic decay has rate -a_s, where
a_s=log(140)+(s-5)log(4)>s+1/3 for s>=7. The denominator has rate s.
The signed-pair estimate thus tends to zero if

  limsup log(tau_sharp_n)/n < 2(a_s-s).

A rate at most 1/2 is sufficient for every fixed s>=7, leaving an upper
rate less than -1/12 for a nonzero selected form. This is a paper
deduction from the established analytic estimates and the displayed
algebraic bound. The asymptotic inequality for tau_sharp itself has not
been proved for the Padé family. This refinement replaces a potentially
overstrong shared-content requirement; it does not resolve that remaining
arithmetic estimate. The subsequent discrete-residue argument closes
the all-index higher-weight augmented-rank proof on paper.

No unconditional irrationality theorem follows from this substitution alone.
