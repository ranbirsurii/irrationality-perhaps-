# Test of the three proposed structural reformulations

The manuscript and Lean theorem claims are unchanged. This pass derives
a valid rational condensation of two complete moment bounds and tests
it. No unconditional irrationality conclusion is obtained.

## Dual-index condensation retaining full normalization

At a fixed weight, write ell(y)=a*zeta(s)+b for y=(a,b). At two eligible
indices the already proved moment bounds give

    ell(y)^2 <= y^T A y,    ell(y)^2 <= y^T B y,

for every rational y, where A and B are the complete positive definite
metrics, including the mass certificate and raw inverse coefficient map.
For rational 0<t<1, define

    H_t=[t*A^(-1)+(1-t)*B^(-1)]^(-1),
    y_1=t*A^(-1)*H_t*y,  y_2=(1-t)*B^(-1)*H_t*y.

Then y_1+y_2=y. Weighted Cauchy--Schwarz and the two source bounds give

    ell(y)^2 <= ell(y_1)^2/t+ell(y_2)^2/(1-t)
              <= y_1^T A y_1/t+y_2^T B y_2/(1-t)
              = y^T H_t y.

This is an exact rational construction, requiring no assumed recurrence
for a singular vector and no irrational eigenvector approximation. If
y is an integer pair, the combined form has exactly those integer
coefficients, even though y_1,y_2 are rational. Thus no denominator is
silently omitted. Gauss reduction of H_t supplies a unimodular pair
of primitive combined forms that cannot simultaneously vanish.
The endpoints t=0,1 recover the two existing source estimates.

The script `dual_index_condensation.py` independently reconstructs A,B
from the stored reduced Gram matrices and unimodular witnesses. It
tests t=0,1/100,1/10,1/2,9/10,99/100,1 at weight seven with first indices
12,20,40,80,160, weight nine with first indices 16,40, and weight eleven
with first index 20. The second index is always n+2. The selected
primitive forms are checked against independent rational zeta enclosures.

In all eight tests the best tested bound is the best original source
bound. No strict improvement is obtained. This is not a proof that
all mixing parameters or all multi-index condensations fail; it is
the outcome of this explicit bounded test. No contraction is inferred.

## Parameter symmetry

For the actual kernel, even n, and odd s, its explicit reflection is

    T_(s,n,m)(-n-t)=-T_(s,n,m)(t).

It follows by reversing the numerator factors and using the odd sign
of the denominator product. If c_(j,q) are the Laurent coefficients,
reflection gives c_(n-j,q)=(-1)^(q+1)c_(j,q). Consequently the total
even-order pole coefficients vanish. Every odd-order sum has the same
reflection character, so this action alone does not separate the
target odd period from the lower odd periods. This symmetry is already
included in the present construction.

[Krattenthaler--Rivoal, Hypergeometrie et fonction zeta de Riemann](https://arxiv.org/pdf/math/0311114),
Theorem 1, proves denominator savings for its explicitly defined
hypergeometric families by identities of Andrews type. It is a relevant
source of possible transformations. We have not constructed a parameter
action or matched theorem hypotheses that supply the proposed savings
for the present combined primitive profiles. No exponent s-2k is
assigned from the order of an unspecified group.

## Prime-local integral projectors

Local integrality can be enforced prime by prime, but the existing
primitive target-pair lattice already describes all rational block
vectors whose final target and constant coefficients are integers.
Replacing a common clearing factor D by D/h and M by M/h gives
F_raw unchanged and leaves the complete primitive cost unchanged.
The common-factor invariance has already been checked in Lean.

A genuinely useful local operator could still exploit an additional
congruence or improve an analytic bound for a new combination. No such
operator with a proved quantitative improvement was constructed here.
No Dwork operator is assumed to act on this family merely because its
coefficients are hypergeometric.

The condensation formula is a valid new bound; its tested instances
do not improve the current one. The other two routes supplied no proved
net saving in this pass. The full negative-rate estimate remains open
in this project, with no new hypotheses inserted into the manuscript.
