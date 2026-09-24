/-
The continuous version of the Gaussian heat potential on a fixed strip, with the
per-point measurability of the version recorded.

`Sandpile.Support.exists_version_continuous_on_strip` (`MeanAKolmogorov.lean`)
builds the same field but discards the measurability of `Y` at each fixed
parameter, since the modification and continuity clauses are all that its own
consumers need.  The polynomial-growth argument needs the measurability too, to
form the events `{ω | ∃ u ∈ box, level < |Y u ω|}` and apply the quantitative
Kolmogorov criterion, so this module reruns the same construction and keeps it.
-/
import Sandpile.Support.MeanAKolmogorov

open MeasureTheory ProbabilityTheory

namespace Sandpile.Support

open Sandpile.Continuum

variable {d : ℕ}

/-- **The Gaussian heat potential has a version on the strip `[0,T]`, continuous at
every sample point and measurable at every parameter.** -/
theorem exists_version_continuous_on_strip_meas (hd : 1 ≤ d) (hd3 : d ≤ 3) {ν2 : ℝ}
    (hν2 : 0 ≤ ν2) {T : ℝ} (hT : 0 < T) {ΩW : Type*} [MeasurableSpace ΩW] (PW : Measure ΩW)
    [IsProbabilityMeasure PW] (W : (Space d → ℝ) → ΩW → ℝ) (hW : IsWhiteNoise d W PW) :
    ∃ Y : ℝ × (Fin d → ℝ) → ΩW → ℝ,
      (∀ z, Measurable (Y z)) ∧
      (∀ z : ℝ × (Fin d → ℝ), z.1 ∈ Set.Icc (0 : ℝ) T →
        Y z =ᵐ[PW] fun ω => gaussianPotential d ν2 W z.1 (WithLp.toLp 2 z.2) ω) ∧
      (∀ ω, Continuous fun z => Y z ω) := by
  obtain ⟨M, hM⟩ := exists_isKolmogorovProcess_potStrip hd hd3 hν2 hT PW W hW
  have hq : ((d : ℝ) + 1) < (d : ℝ) + 2 := by linarith
  obtain ⟨Y, hYmeas, hYmod, hYcont⟩ :=
    LatticeProb.exists_continuous_modification_spaceTime_all hM hq
  refine ⟨Y, hYmeas, fun z hz => ?_, hYcont⟩
  have h := (hYmod z).symm
  have heq : potStrip d ν2 W T z
      = fun ω => gaussianPotential d ν2 W z.1 (WithLp.toLp 2 z.2) ω := by
    funext ω
    show gaussianPotential d ν2 W (clampTimeK T z.1) (WithLp.toLp 2 z.2) ω
      = gaussianPotential d ν2 W z.1 (WithLp.toLp 2 z.2) ω
    rw [clampTimeK_eq_self hz.1 hz.2]
  rwa [heq] at h

end Sandpile.Support
