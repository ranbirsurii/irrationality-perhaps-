# Recentring the signed-prefix approximation

The exact prefix is absorbed into the rational centre, leaving only
the certified tail in the radius. The interval inclusion is proved by
an exact identity. For every integer linear form, the interval majorant
is monotone under this refinement. Retaining the previous pair therefore
guarantees that the optimized new bound is no larger, even when that
retained pair is not consecutive for the corrected centre.

For each prescribed b>1, the existing cutoff argument can ensure a
tail at most b^(-n). The nonzero integer coefficient p0 has abs(p0)>=1,
so the corrected radius is also at most b^(-n). The centres and cutoffs
depend on b. This is a uniform accuracy construction, not a uniform
decay theorem for the integer forms: the convergent gaps remain relevant.

The script recentered_cf_root.py passes ten actual profiles, thirty
signed-prefix certificates and twelve rational-target controls.
Independent zeta enclosures check all signed intervals; they do not
select the pairs. Every tested profile verifies 8^n E_new<E_old by
exact rational arithmetic. Thus the tested epsilon gains exceed log8.
The weight-seven bounds printed in the manuscript are also checked
with exact rational thresholds. These finite gains are not extrapolated.

Four new Lean lemmas verify the correction, the radius identity, the
integer-radius comparison, and interval-majorant monotonicity. The
full factorial-family, adaptive cutoff and continued-fraction selection
applications are paper arguments. The all-index non-worsening result
does not prove a uniform strict gain or all-odd irrationality.

The changed module and verification driver compiled successfully. The
driver records sixteen theorem dependency reports. The four new lemmas
use only propext, Classical.choice and Quot.sound, with no sorryAx.
The previous thirty-certificate compression check also passes after
the shared certificate interface was extended. The existing manuscript
compiled successfully after the derivation was added in place. No
fresh full-library rebuild is claimed.
