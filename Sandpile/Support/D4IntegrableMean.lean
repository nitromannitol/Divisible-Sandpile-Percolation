import Sandpile.Support.ConvexProjection
import Sandpile.Frozen.CriticalTopplingD4
import Sandpile.External.VarianceScaleProved

/-!
# The logarithmic mean lower bound for integrable scenery in dimension four

The logarithmic lower bound for centered integrable nondegenerate scenery,
`cor:d4-logarithmic-mean-lower` of `sandpile.tex:2962-2990`. Projecting onto a negative half-line
and its complement gives a bounded centered law; conditional Jensen transfers the logarithmic lower
bound from that law to the original one. The single theorem `exists_log_mean_lower_integrable_four`
builds the bounded projected law `binaryProjection`, applies the already-proved critical toppling
estimate `Sandpile.Frozen.critical_toppling_d4` to it, and transfers the resulting logarithmic mean
bound back to the original law via `meanOdometerOf_binaryProjection_le`.
-/

open MeasureTheory ProbabilityTheory

namespace Sandpile

/-- The logarithmic mean lower bound requires only a centered, integrable, nondegenerate law. -/
theorem exists_log_mean_lower_integrable_four (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable id ν) (hmean : ∫ z, z ∂ν = 0) (hnondeg : 0 < evariance id ν) :
    ∃ c : ℝ, 0 < c ∧ ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
      c * Real.log t ≤ meanOdometer (centeredMassLaw 4 ν) t := by
  have hnot : ∀ z : ℝ, ν ≠ Measure.dirac z := by
    intro z hν
    have hzero : evariance id (Measure.dirac z) = 0 := by simp [evariance]
    rw [hν, hzero] at hnondeg
    exact (lt_irrefl _ hnondeg)
  obtain ⟨a, ha, hpa⟩ := exists_left_tail_pos ν hint hmean hnot
  set f := binaryProjection ν (Set.Iic (-a))
  set ρ := ν.map f
  obtain ⟨hρ, hmρ, hvρ, hiρ⟩ := binaryProjection_law_properties ν hint hmean a ha hpa
  haveI : IsProbabilityMeasure ρ := hρ
  obtain ⟨r, hr0, hrpos, hrvar⟩ := ENNReal.lt_iff_exists_real_btwn.mp hvρ
  have hr : 0 < r := ENNReal.ofReal_pos.mp hrpos
  have hvr : ENNReal.ofReal ((Real.sqrt r) ^ 2) ≤ evariance id ρ := by
    rw [Real.sq_sqrt hr0]
    exact hrvar.le
  set K := ∫ z, Real.exp |z| ∂ρ
  obtain ⟨c, C, hc, _, t₀, hb⟩ := Sandpile.Frozen.critical_toppling_d4
    (Real.sqrt r) 1 K (Real.sqrt_pos.mpr hr) (by norm_num)
  have hlo := (hb ρ ‹_› hmρ hvr (by simpa using hiρ) (by simp [K])).1
  refine ⟨c, hc, t₀, fun t ht => ?_⟩
  have hl : c * Real.log t ≤ meanOdometer (centeredMassLaw 4 ρ) t := (hlo t ht).1
  rw [meanOdometer_eq 4 ρ (by norm_num) t] at hl
  rw [meanOdometer_eq 4 ν (by norm_num) t]
  exact hl.trans (meanOdometerOf_binaryProjection_le ν hint measurableSet_Iic t (0 : Site 4))

end Sandpile
