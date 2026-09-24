/-
The roadmap of Step 2 of `thm:dgt4-many-limits` (`sandpile.tex:6051-6275`), and
where each of its three parts lives.

(i) The origin-fixed concentration `eq:dgt4-band-origin-fixed-concentration` and
lower tail `eq:dgt4-band-origin-fixed-lower-tail` reduce both conclusions to
replacing `Pw_n(0)` by `E u_n(0)/G(0,0)`.  Both are PROVED, about
`W_n = avg (originOdometer (scenery d σ) n) 0`, as
`Sandpile.Support.band_origin_concentration` and
`Sandpile.Support.band_origin_lower_tail`
(`Sandpile/Support/Dgt4ABandConcentration.lean`).  An earlier transcription of
them as a predicate `BandStep2Input` read the FIXED scenery value at the origin
instead of `W_n`, which makes it false; it has been deleted, and the refutation
is kept as `Sandpile/Support/Dgt4ABandStep2Refuted.lean`.

(ii) The band profile `eq:dgt4-band-profile`, the density bound
`eq:dgt4-band-density` and the two isolation estimates give the integrated
profile `eq:dgt4-band-integrated-profile` (`Dgt4ABandIntegrated.lean`) and then
the one-step profile `eq:dgt4-band-one-step-profile`
(`Dgt4ABandOneStep.lean`), whose summation is `eq:dgt4-band-summed-profile` and
whose inversion is the scaled profile `eq:dgt4-band-scaled-profile`
(`Dgt4ABandScaled.lean`), with the weights `L_k` of `sandpile.tex:6092-6095`
supplied by `Dgt4ABandSlowWeights.lean`.

(iii) The scaled profile and the band profile give the contact rate
`eq:dgt4-band-contact-rate`, and the contact error
`eq:dgt4-band-contact-error` gives the comparison
`eq:dgt4-band-contact-comparison`; both are named in `Dgt4ABand.lean` in the
sequence-indexed form that Step 3 consumes, and their deterministic-level content
is `Dgt4ABandReplacement.lean`.
-/
import Sandpile.Support.Dgt4ABandLaw
import Sandpile.Support.Dgt4ABand
import Sandpile.Support.Dgt4ABandScaled
