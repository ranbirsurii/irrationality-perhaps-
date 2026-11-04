# Coarse prime sieve continuation

The full paper derivation is included in the current manuscript as
`publication/high-weight-criterion/coarse-hankel-prime-sieve.tex`.

For fixed odd weight s, the integer-valued basis argument in the
weight-five source extends to the positive powered Hankel polynomial
F_(s,K)=S_K Delta_(s,K). At K=40n,N=3n,h=37n, it gives

    v_p^G(F_(s,K)) >= -(s+1)h floor(log_p(5K)) - h v_p((s-1)!).

The proof uses the binomial basis, s-2 derivatives of the polynomial
part, one Bernoulli-functional denominator, and the order-s harmonic
pole term. The normalizing scalar S_K is the same for all fixed weights.

Clearing just p<=K/M has asymptotic log cost per K^2 exactly

    37(s+1)/(40M).

For weight seven this is 7.4/M. It is below any prescribed epsilon
when the fixed cutoff M is chosen sufficiently large. The sum is
evaluated by counting prime powers; only the first powers have a
linear-in-K contribution. Higher powers contribute o(K).

This proves small-prime control for explicit sufficient local clearing
factors. It does not estimate the difference of two primitive monic
denominators. The relative cost of the explicit factors is instead
37(s-5)/(40M), and is labeled accordingly in the manuscript.

Using the same coarse bound at all primes incurs exponent 37 at
weight seven, which does not yield the required negative total upper
rate. The middle prime bands still require a sharper estimate.

The exact checker reconstructs twelve actual rational Hankel polynomials
at weights 5,7,9, checks their leading coefficients and an additional
integer evaluation, and verifies 178 local valuation bounds.
This section is a paper proof; no new complete Lean proof of the
powered Hankel construction or of irrationality is claimed.

The two newly requested chats were read:

- Bombieri Vinogradov Twin Primes: its final shifted covariance estimate
  is explicitly unproved; the marginal estimates do not determine it.
- Prove Sextic Spectral Bound: its latest cubic mollifier identities
  preserve the structured problem, but the decisive signed mean-value
  saving remains unproved. These are Hecke characters over Eisenstein
  ideals, not the prime valuations of the Hankel coefficients.

No substitution of either unproved endpoint has been made. Classical
Bombieri-Vinogradov would require an actual small-modulus description
of the determinant defect before it could estimate the exceptional
prime weight. No such description is currently proved in this project.
