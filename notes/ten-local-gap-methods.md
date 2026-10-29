# Ten literature methods for the local gap, with their actual hypotheses

Goal: at the moving slope theta_n, control the partial quotient a_n^*
where consecutive convergent denominators bracket H_n. This is the
original sequence index n, not continued-fraction depth.

The valid local proof is self-contained. For q<=H<=Q choose V=q or Q
nearest on the logarithmic scale. Then

    lambda^2+lambda^(-2)<=2Q/q<=2(a_n^*+1),
    R_n<=40(a_n^*+1)4^(-n).

The recurrence is Q=a_n^* q+q_previous with 0<=q_previous<=q.
If H^2<=qQ use V=q; otherwise use V=Q. In the first case both
q^2/H^2 and H^2/q^2 are <=Q/q, and in the second both corresponding
terms for Q are <=Q/q. Lean verifies these algebraic implications.
If a rational continued fraction ends before H, this bracket proof does
not apply; the terminal undershoot remains in the earlier lambda bound.

| Method and primary source | What is valid | Application to this family |
| --- | --- | --- |
| 1. Continued-fraction recurrence and nearest-denominator selection; explicit proof above | A local quotient controls the bracket distortion. | Gives the displayed inequality, but does not bound a_n^* as n grows or ensure a bracket before rational termination. |
| 2. [Levy, continued fractions of a randomly chosen number (1936)](https://www.numdam.org/item/CM_1936__3__286_0/) | A metrical asymptotic for almost every fixed real slope. | No typicality theorem for these particular moving rational slopes is proved. |
| 3. [Roth, rational approximations to algebraic numbers (1955)](https://www.cambridge.org/core/journals/mathematika/article/rational-approximations-to-algebraic-numbers/EFB89E2873019B246F004FAA06E05A7F) | Strong approximation bounds for algebraic irrational numbers. | Neither the required algebraicity/irrationality identification nor a uniform bound for these moving slopes follows. Assuming the target is algebraic irrational already assumes its irrationality. |
| 4. [Kleinbock, quantitative nondivergence](https://www.claymath.org/library/proceedings/cmip010c.pdf) | Bounds for specified families of lattice trajectories under quantitative hypotheses. | No qualifying trajectory and hypotheses giving the needed pointwise cusp control for this sequence have been established. Measure bounds do not automatically bound a prescribed point. |
| 5. [Ben David et al., polynomial continued fractions and factorial reduction (2024)](https://link.springer.com/article/10.1007/s40598-024-00250-z) | Theorems connect recurrence growth, gcd reduction and approximation quality; additional classification claims are explicitly conjectures. | No proved polynomial continued-fraction identity with the required gcd reduction and isolated target is identified here. Empirical factorial reduction is not used as a theorem. |
| 6. [Odlyzko, discriminant bounds (1990)](https://www.numdam.org/item/JTNB_1990__2_1_119_0.pdf) | Discriminant bounds and related estimates with specified assumptions. | The constructed quadratic-order ideal gives an exact norm formula, but a lower field-discriminant bound does not give the required lower bound on its least represented norm or control its conductor. |
| 7. [Fischler, Siegel-lemma odd-zeta construction](https://arxiv.org/abs/2109.10136) | Quantitative linear independence in a span of many odd zeta values. | Does not assert irrationality of every prescribed odd value or produce the required two short primitive images in its target quotient. |
| 8. [Lai, elimination and Phi_n arithmetic factors (2025)](https://arxiv.org/abs/2501.05321) | An improved lower bound on the number of irrational odd zeta values. | Its elimination and arithmetic factors are genuine tools, but its conclusion does not isolate every target, and the required factor identification for these coefficient rows is absent. |
| 9. [Fischler-Rivoal, rational approximation to G-function values](https://www.imo.universite-paris-saclay.fr/~stephane.fischler/approxG.pdf) | Effective estimates at suitable small rational arguments with function-dependent thresholds. | No qualifying substitution, arithmetic transfer and threshold verification identifying the target zeta value are proved. The endpoint 1 is not automatically covered. |
| 10. [Brown, Mellin transforms and transfinite diameter (2026)](https://arxiv.org/html/2604.20741v1) | A higher-dimensional period irrationality criterion requiring an analytic diameter bound and arithmetic clearing data. | No complete two-period realization with the required clearing and diameter bounds for each target is constructed here. |

These are ten legitimate mathematical approaches, not ten verified
applications proving this target. The closest applicable route is 1:
its local reduction is proved, while its family-specific growth estimate
remains open in this project. None of the checked sources supplies that
missing estimate under hypotheses already proved here.

## Limsup principles and the exact conclusion they allow

For positive R_n and a_n^*+1, on indices where the bracket exists,

    log R_n/n <= log(40)/n-log(4)+log(a_n^*+1)/n.

Taking extended-real upper limits gives

    limsup log R_n/n <= -log(4)+limsup log(a_n^*+1)/n.

Thus a proved upper rate gamma<log(4) implies a negative upper rate
at most -(log(4)-gamma). For every 0<epsilon<log(4)-gamma, the
definition of limsup then gives R_n<=exp(-epsilon*n) eventually.
This is the valid limsup closure. It includes polynomial and
subexponential local quotient bounds in the original index n.

Neither the upper bound gamma<log(4) for the actual selected quotients
nor adequate terminal-case control has been proved. Limsup algebra
cannot replace either arithmetic estimate. No unconditional all-odd
irrationality theorem follows from this literature comparison.

The current Lean additions prove the local denominator-ratio bound and
nearest-denominator balance inequality. The existing exponential-envelope
smallness theorem supplies the abstract limit implication once a valid
arithmetic growth envelope is supplied. No missing envelope is inserted
as an axiom or stated as an established family theorem.
