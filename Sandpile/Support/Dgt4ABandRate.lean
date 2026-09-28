import Sandpile.Support.Dgt4ABand
import Sandpile.Support.Dgt4Thresholds

/-!
# The band contact rate from the pointwise threshold asymptotic

`BandContactRate` follows from the pointwise threshold asymptotic: the threshold probability at
the level `E u_{n-1}(0)` is `G(0,0)κ/n` to leading order, uniformly over the band
`δ R_k^2 ≤ n ≤ ⌊R_k^2 T⌋`. The band estimate is read here along a constant exponent sequence,
because a pointwise asymptotic fixes one `κ`; the varying exponents of the band construction are
supplied elsewhere, not by this passage.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile.Support

open Sandpile

/-- The first clause of `PointwiseContactThresholds` gives the band-uniform
threshold asymptotic `eq:dgt4-band-contact-rate` along every divergent sequence
of scales, because `δ R_k^2 → ∞`. -/
theorem bandContactRate_of_pointwise (d : ℕ) (ν : Measure ℝ) (κ T : ℝ) (hκ : 0 < κ)
    (hG : 0 < Sandpile.green d 0 0) (Rseq : ℕ → ℝ) (hRtop : Tendsto Rseq atTop atTop)
    (h : Tendsto (fun m : ℕ => (m : ℝ) * ((Sandpile.centeredMassLaw d ν)
          {σ | Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) (m - 1) <
            -(Sandpile.green d 0 0 * Sandpile.scenery d σ 0)}).toReal /
        (Sandpile.green d 0 0 * κ)) atTop (𝓝 1)) :
    BandContactRate d ν (fun _ => κ) Rseq T := by
  intro δ hδ η hη
  have hκne : κ ≠ 0 := ne_of_gt hκ
  have hGne : Sandpile.green d 0 0 ≠ 0 := ne_of_gt hG
  have h' : Tendsto (fun m : ℕ => (m : ℝ) * ((Sandpile.centeredMassLaw d ν)
        {σ | Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) (m - 1) <
          -(Sandpile.green d 0 0 * Sandpile.scenery d σ 0)}).toReal /
      Sandpile.green d 0 0) atTop (𝓝 κ) := by
    have hc := h.const_mul κ
    rw [mul_one] at hc
    refine hc.congr fun m => ?_
    field_simp
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp h' η hη
  have hsq : Tendsto (fun k : ℕ => Rseq k ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hRtop
  have hbig : ∀ᶠ k : ℕ in atTop, (M : ℝ) ≤ δ * Rseq k ^ 2 :=
    (Filter.Tendsto.const_mul_atTop hδ.1 hsq).eventually_ge_atTop M
  filter_upwards [hbig] with k hk n hn1 _
  have hnM : M ≤ n := by
    have h2 : (M : ℝ) ≤ (n : ℝ) := le_trans hk hn1
    exact_mod_cast h2
  have hA := hM n hnM
  rw [Real.dist_eq] at hA
  exact le_of_lt hA

end Sandpile.Support
