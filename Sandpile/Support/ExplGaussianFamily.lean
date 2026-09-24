/-
Stopped Gaussian increments simultaneously over starting points.

The common noise event is supplied by the field semigroup and continuity before
choosing any motion from the family. Thus all starting points, horizons and
bounded natural stopping times share the stopped-increment identity.
-/
import Sandpile.Support.ExplGaussianHorizon
open MeasureTheory ProbabilityTheory Filter Topology LatticeProb
open scoped ENNReal NNReal
namespace Sandpile.Support
open Sandpile.Continuum
theorem gaussianPotential_stopped_increment_integral_family {ΩW ΩB : Type*}
    [MeasurableSpace ΩW] [MeasurableSpace ΩB] {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3)
    {PW : Measure ΩW} [IsProbabilityMeasure PW] {W : (Space d → ℝ) → ΩW → ℝ}
    (hW : IsWhiteNoise d W PW) (ν2 : ℝ) (Z : ℝ → Space d → ΩW → ℝ)
    (hmod : ∀ t : ℝ, 0 ≤ t → ∀ x, Z t x =ᵐ[PW] gaussianPotential d ν2 W t x)
    (hc : ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂PW,
      ContinuousOn (fun q : ℝ × Space d => Z q.1 q.2 ω) (Set.Icc 0 T ×ˢ Set.univ))
    {PB : Measure ΩB} [IsProbabilityMeasure PB] (B : Space d → ℝ≥0 → ΩB → Space d)
    (hB : ∀ x, IsBrownian d x (B x) PB) (hBm : ∀ x r, StronglyMeasurable (B x r))
    (hBc : ∀ x b, Continuous fun r => B x r b) :
    ∀ᵐ ω ∂PW, ∀ x : Space d, ∀ t δ : ℝ≥0, ∀ τ : ΩB → ℝ≥0,
      IsBrownianStopping (B x) τ → (∀ b, τ b ≤ t) →
      Integrable (fun b => Z (t - τ b + δ : ℝ≥0) (B x (τ b) b) ω -
        Z (t - τ b : ℝ≥0) (B x (τ b) b) ω) PB ∧
      (∫ b, Z (t - τ b + δ : ℝ≥0) (B x (τ b) b) ω -
        Z (t - τ b : ℝ≥0) (B x (τ b) b) ω ∂PB) = Z (t + δ) x ω - Z t x ω := by
  have hcont : ∀ᵐ ω ∂PW, Continuous fun q : ℝ≥0 × Space d => Z q.1 q.2 ω := by
    have hh := ae_all_iff.mpr (fun n : ℕ => hc ((n : ℝ) + 1) (by positivity))
    exact hh.mono fun ω hω => continuous_nonnegative_time_of_bounded_strips (fun t x => Z t x ω) hω
  filter_upwards [gaussianPotential_increment_semigroup_common hd hd3 hW ν2 Z hmod hc, hcont] with ω hs hz
  intro x t δ τ hτ hτt
  let M (r : ℝ≥0) (b : ΩB) := Z (t - min r t + δ : ℝ≥0) (B x (min r t) b) ω -
    Z (t - min r t : ℝ≥0) (B x (min r t) b) ω
  have hm : Martingale M (natFiltration (B x) (hBm x)) PB := by
    apply brownian_heat_semigroup_martingale hd (hB x) (hBm x) (hBc x)
      (fun s y => Z (s + δ : ℝ≥0) y ω - Z s y ω) ?_ ?_ t
    · exact (hz.comp ((continuous_fst.add continuous_const).prodMk continuous_snd)).sub hz
    · intro r hr s z
      simpa only [NNReal.coe_add, add_assoc] using hs r s δ hr s.property δ.property z
  have hMc : ∀ b, Continuous fun r => M r b := by
    intro b
    exact (hz.comp (((continuous_const.sub (continuous_id.min continuous_const)).add continuous_const).prodMk
      ((hBc x b).comp (continuous_id.min continuous_const)))).sub
        (hz.comp ((continuous_const.sub (continuous_id.min continuous_const)).prodMk
          ((hBc x b).comp (continuous_id.min continuous_const))))
  have hi := integrable_stopped_martingale_eq_of_continuous PB (natFiltration (B x) (hBm x)) M hm
    hMc τ ((isBrownianStopping_iff_natFiltration (B x) (hBm x) τ).mp hτ) t hτt
  have he : (fun b => M (τ b) b) = (fun b => Z (t - τ b + δ : ℝ≥0) (B x (τ b) b) ω -
      Z (t - τ b : ℝ≥0) (B x (τ b) b) ω) := by
    funext b
    simp only [M, min_eq_left (hτt b)]
  rw [← he]
  refine ⟨hi.1, hi.2.trans ?_⟩
  calc
    (∫ b, M 0 b ∂PB) = ∫ _ : ΩB, Z (t + δ) x ω - Z t x ω ∂PB := by
      apply integral_congr_ae
      filter_upwards [(hB x).start] with b hb
      simp [M, hb]
    _ = Z (t + δ) x ω - Z t x ω := by simp

theorem gaussianPotential_horizonFreeIncrement_family_of_stopped_integrability {ΩW ΩB : Type*}
    [MeasurableSpace ΩW] [MeasurableSpace ΩB] {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3)
    {PW : Measure ΩW} [IsProbabilityMeasure PW] {W : (Space d → ℝ) → ΩW → ℝ}
    (hW : IsWhiteNoise d W PW) (ν2 : ℝ) (Z : ℝ → Space d → ΩW → ℝ)
    (hmod : ∀ t : ℝ, 0 ≤ t → ∀ x, Z t x =ᵐ[PW] gaussianPotential d ν2 W t x)
    (hc : ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂PW,
      ContinuousOn (fun q : ℝ × Space d => Z q.1 q.2 ω) (Set.Icc 0 T ×ˢ Set.univ))
    {PB : Measure ΩB} [IsProbabilityMeasure PB] (B : Space d → ℝ≥0 → ΩB → Space d)
    (hB : ∀ x, IsBrownian d x (B x) PB) (hBm : ∀ x r, StronglyMeasurable (B x r))
    (hBc : ∀ x b, Continuous fun r => B x r b) :
    ∀ᵐ ω ∂PW, ∀ x : Space d, ∀ t T : ℝ≥0, t ≤ T →
      (∀ τ : ΩB → ℝ≥0, IsBrownianStopping (B x) τ → (∀ b, τ b ≤ t) →
        Integrable (fun b => Z ((t : ℝ) - τ b) (B x (τ b) b) ω) PB) →
      HorizonFreeIncrement (B x) PB (fun s y => Z s y ω) t T x := by
  filter_upwards [gaussianPotential_stopped_increment_integral_family hd hd3 hW ν2 Z hmod hc B hB hBm hBc] with ω hω
  intro x t T htT hI τ hτ hτt
  have hbt : ∀ b, τ b ≤ t := hτt
  have hinc := hω x t (T - t) τ hτ hbt
  have he (b : ΩB) : (t - τ b + (T - t) : ℝ≥0) = T - τ b := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_add, NNReal.coe_sub (hbt b), NNReal.coe_sub htT,
      NNReal.coe_sub ((hbt b).trans htT)]
    ring
  have hsum : (t : ℝ) + (T - t : ℝ≥0) = (T : ℝ) := by
    rw [NNReal.coe_sub htT]
    ring
  simp_rw [he, hsum, NNReal.coe_sub (hbt _), NNReal.coe_sub ((hbt _).trans htT)] at hinc
  have hi := hI τ hτ hbt
  have hiT : Integrable (fun b => Z ((T : ℝ) - τ b) (B x (τ b) b) ω) PB := by
    have hh := hinc.1.add hi
    simpa only [Pi.add_def, sub_add_cancel] using hh
  have hh := hinc.2
  rw [integral_sub hiT hi] at hh
  change Z t x ω + (∫ b, -Z ((t : ℝ) - τ b) (B x (τ b) b) ω ∂PB) =
    Z T x ω + ∫ b, -Z ((T : ℝ) - τ b) (B x (τ b) b) ω ∂PB
  rw [integral_neg, integral_neg]
  linarith

end Sandpile.Support
