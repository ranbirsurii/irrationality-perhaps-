# Ten-method literature and limsup continuation

The note ten-local-gap-methods.md compares ten legitimate methods with
primary-source links and the hypotheses actually needed here. This is
not a claim that ten theorems prove the target. No checked source supplies
the unproved local partial-quotient rate under established hypotheses.

Two new statements in BinaryGaussCertificate.lean compile: the local
denominator-ratio bound and the nearest-denominator balance inequality.
The driver lists only propext, Classical.choice and Quot.sound for them.
No added mathematical axiom or sorryAx occurs. The existing exponential
smallness theorem supports the abstract rate-to-limit step; no actual
arithmetic growth envelope is assumed to have been established.

On indices admitting a convergent bracket, the paper obtains
R_n<=40(a_n^*+1)4^(-n), and hence the upper logarithmic rate is at most
-log(4)+limsup log(a_n^*+1)/n. A rate strictly below log(4) would conclude
decay. That arithmetic rate and the rational terminal case remain
unproved for the actual family. The unconditional theorem is not claimed.

The existing main.tex was edited in place, with references and the
conditional limsup derivation, and compiled successfully with the
desktop editor. No replacement PDF or fresh full-project Lean build
is claimed by this record.
