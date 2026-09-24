/-
`eq:dgt4-band-contact-comparison` (`sandpile.tex:6278-6292`) from the second
clause of `PointwiseContactThresholds`: the contact event `{u_n(0)=0}` agrees
with the threshold event up to `o(1/n)`, uniformly over the band
`δ R_k^2 ≤ n ≤ ⌊R_k^2 T⌋`.

Over the band `R_k^2 ≤ n/δ`, so the `n`-normalized pointwise estimate gives the
scale-normalized band estimate that `uniformContactThresholdsAlong_of_band`
consumes.
-/
import Sandpile.Support.Dgt4ABand
import Sandpile.Support.Dgt4Thresholds

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile.Support

open Sandpile

/-- The second clause of `PointwiseContactThresholds` gives the band-uniform
contact comparison `eq:dgt4-band-contact-comparison` along every divergent
sequence of scales, because `δ R_k^2 → ∞` and `R_k^2 ≤ n/δ` over the band. -/
theorem bandContactComparison_of_pointwise (d : ℕ) (ν : Measure ℝ) (T : ℝ) (_hT : 0 < T)
    (Rseq : ℕ → ℝ) (hRtop : Tendsto Rseq atTop atTop)
    (h : Tendsto (fun m : ℕ => (m : ℝ) * ((Sandpile.centeredMassLaw d ν)
        (symmDiff {σ | Sandpile.odometer σ m 0 = 0}
          {σ | Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) (m - 1) <
            -(Sandpile.green d 0 0 * Sandpile.scenery d σ 0)})).toReal) atTop (𝓝 0)) :
    BandContactComparison d ν Rseq T := by
  intro δ hδ η hη
  have hδ0 : 0 < δ := hδ.1
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp h (δ * η) (by positivity)
  have hsq : Tendsto (fun k : ℕ => Rseq k ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hRtop
  have hbig : ∀ᶠ k : ℕ in atTop, (M : ℝ) ≤ δ * Rseq k ^ 2 :=
    (Filter.Tendsto.const_mul_atTop hδ0 hsq).eventually_ge_atTop M
  filter_upwards [hbig] with k hk n hn1 _
  set Q : ℝ := ((Sandpile.centeredMassLaw d ν)
      (symmDiff {σ | Sandpile.odometer σ n 0 = 0}
        {σ | Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) (n - 1) <
          -(Sandpile.green d 0 0 * Sandpile.scenery d σ 0)})).toReal with hQ
  have hQnn : 0 ≤ Q := ENNReal.toReal_nonneg
  have hnM : M ≤ n := by
    have h2 : (M : ℝ) ≤ (n : ℝ) := le_trans hk hn1
    exact_mod_cast h2
  have hA := hM n hnM
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg n) hQnn)] at hA
  have hRQ : δ * (Rseq k ^ 2 * Q) ≤ (n : ℝ) * Q := by
    have hmul := mul_le_mul_of_nonneg_right hn1 hQnn
    nlinarith [hmul]
  nlinarith [hA, hRQ, hδ0]

end Sandpile.Support
