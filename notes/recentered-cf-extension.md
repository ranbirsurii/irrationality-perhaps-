# Continuing the corrected-center construction

The script `scripts/recentered_cf_extension.py` extends the earlier exact
certificate calculation to four additional weight/index pairs. It uses
the same adjugate root forms, signed prefixes, tail bounds, interval
recentering, and unimodular pair selection. It introduces no distribution
or holonomy hypothesis.

| Weight | Index | Strict common upper bound for the two integer forms |
|---|---|---|
| 7 | 24 | 6 times 10^(-92) |
| 7 | 28 | 2 times 10^(-106) |
| 13 | 12 | 2 times 10^(-79) |
| 15 | 14 | 9 times 10^(-101) |

All four displayed bounds are checked by rational comparisons. For each
profile the selected pair has determinant of absolute value one. Hence
its two forms cannot both vanish. Signed-prefix intervals additionally
identify at least one nonzero form. There are twelve signed-prefix
certificates, and twelve rational-target negative controls are repeated.
Each new profile also passes the previous strict finite improvement test
E_new times 8^n < E_old.

These are finite certificates, not a proof of uniform decay. The remaining
quantity is the explicitly computed interval cost

    E_n = min over retained and new unimodular pairs
          max_i (|Q_i c_n - P_i| + Q_i delta_n).

The already proved corrected radius estimate allows delta_n <= b^(-n)
for any fixed b > 1, with a corresponding change in the center and cutoff.
It does not bound the denominators of the selected pair. Thus the present
calculation continues the existing construction but does not establish
the irrationality of every odd zeta value. No extra Lean theorem is
claimed for these Python certificate computations.
