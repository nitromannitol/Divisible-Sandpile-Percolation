import Sandpile.Support.Dgt4ABand
import Sandpile.Support.Dgt4ABandRate
import Sandpile.Support.Dgt4ABandComp
import Sandpile.Support.Dgt4ABandSequence

/-!
# The Step-2 output of the many-limits theorem, packaged for Step 3

The Step-2 output of `thm:dgt4-many-limits` (`sandpile.tex:6051-6275`), in the form the frozen
Step-3 chain consumes. Step 2 proves the two band limits `eq:dgt4-band-contact-rate` and
`eq:dgt4-band-contact-comparison` at the exponent `κ_k = 1 + 1/ϑ_k` of the constructed
scenery, uniformly over the band `δ R_k^2 ≤ n ≤ T R_k^2`. The exponents move with the scale,
so both limits are read along the sequence of scales `R_k` against the sequence of exponents
`κ_k`. Step 3 (`sandpile.tex:6275-6305`) fixes `κ ∈ [3/2,2]`, extracts `k_ℓ ↑ ∞` with
`κ_{k_ℓ} → κ`, and reads the two limits along `R_{k_ℓ}`; the uniform contact-threshold
estimate `eq:dgt4-uniform-contact-thresholds` is what `lem:dgt4-path-survival` assumes.
`Dgt4AStep2Output d ν kseq Rseq` packages that output, and
`uniformContactThresholdsAlong_of_step2` extracts the uniform contact-threshold estimate
along `Rseq` from it.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile.Support

open Sandpile

/-- The Step-2 output of `thm:dgt4-many-limits` (`sandpile.tex:6046-6270`): for
every horizon `T > 0`, the two band limits `eq:dgt4-band-contact-rate` and
`eq:dgt4-band-contact-comparison` hold along the scales `Rseq` against the
exponents `kseq`. -/
def Dgt4AStep2Output (d : ℕ) (ν : Measure ℝ) (kseq Rseq : ℕ → ℝ) : Prop :=
  ∀ T : ℝ, 0 < T → BandContactRate d ν kseq Rseq T ∧ BandContactComparison d ν Rseq T

/-- **The uniform contact-threshold estimate from the Step-2 output.**  The two
band limits at `δ = ε T/2` give `eq:dgt4-uniform-contact-thresholds` along the
same scales, the hypothesis of the frozen `lem:dgt4-path-survival`. -/
theorem uniformContactThresholdsAlong_of_step2 (d : ℕ) (ν : Measure ℝ)
    (kseq Rseq : ℕ → ℝ) (hRtop : Tendsto Rseq atTop atTop) (κ T : ℝ) (hκ : 0 < κ)
    (hT : 0 < T) (hkseq : Tendsto kseq atTop (𝓝 κ))
    (h : Dgt4AStep2Output d ν kseq Rseq) :
    UniformContactThresholdsAlong d ν κ T Rseq :=
  uniformContactThresholdsAlong_of_band d ν Rseq kseq hRtop κ T hκ hT hkseq
    (h T hT).1 (h T hT).2

end Sandpile.Support
