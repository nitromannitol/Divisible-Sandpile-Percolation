/-
Backward heat increments along Brownian motion.

The continuous Gaussian field satisfies the homogeneous increment semigroup on
one common noise event. Brownian transition densities and strong Markov restart
make these increments martingales. Bounded optional sampling gives the stopped
increment identity simultaneously for every bounded natural stopping time.
-/
import Sandpile.Support.ExplHeatDom
import Sandpile.Support.ExplBrownianDensity
import Sandpile.Support.ExplBrownianSemigroup
import Sandpile.Support.ExplOptionalUniform
open MeasureTheory ProbabilityTheory Filter Topology LatticeProb
open scoped ENNReal NNReal
namespace Sandpile.Support
open Sandpile.Continuum

theorem brownian_heat_semigroup_martingale {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (hd : 1 ≤ d) {P : Measure Ω} [IsProbabilityMeasure P] {x : Space d}
    {B : ℝ≥0 → Ω → Space d} (hB : IsBrownian d x B P)
    (hBm : ∀ r, StronglyMeasurable (B r)) (hBc : ∀ b, Continuous fun r => B r b)
    (H : ℝ≥0 → Space d → ℝ) (hH : Continuous fun q : ℝ≥0 × Space d => H q.1 q.2)
    (hS : ∀ r : ℝ≥0, 0 < r → ∀ s : ℝ≥0, ∀ z : Space d,
      Integrable (fun y => Continuum.heatKernelBM d r z y * H s y) volume ∧
        (∫ y, Continuum.heatKernelBM d r z y * H s y) = H (r + s) z)
    (t : ℝ≥0) :
    Martingale (fun r b => H (t - min r t) (B (min r t) b)) (natFiltration B hBm) P := by
  have hHm (s : ℝ≥0) : Measurable (H s) :=
    (hH.comp (continuous_const.prodMk continuous_id)).measurable
  apply brownian_backward_semigroup_martingale hB hBm hBc H hHm t
  · intro r hrt
    by_cases hr : r = 0
    · apply (integrable_const (H t x)).congr
      filter_upwards [hB.start] with b hb
      simp [hr, hb]
    · have hr' : 0 < r := bot_lt_iff_ne_bot.mpr hr
      have hi := (brownian_transition_integral hd hB r hr' x (H (t - r)) (hHm _)
        (hS r hr' (t - r) x).1).1
      apply hi.congr
      filter_upwards [hB.start] with b hb
      simp [hb]
  · intro r u hru hut z
    by_cases he : r = u
    · subst u
      simp
    · have hpos : 0 < u - r := tsub_pos_iff_lt.mpr (lt_of_le_of_ne hru he)
      have hh := (brownian_transition_integral hd hB (u - r) hpos z (H (t - u))
        (hHm _) (hS (u - r) hpos (t - u) z).1).2
      rw [hh, (hS (u - r) hpos (t - u) z).2]
      congr 1
      apply NNReal.coe_injective
      simp only [NNReal.coe_add, NNReal.coe_sub hru, NNReal.coe_sub hut, NNReal.coe_sub (hru.trans hut)]
      ring

theorem gaussianPotential_backward_increment_martingale {ΩW ΩB : Type*}
    [MeasurableSpace ΩW] [MeasurableSpace ΩB] {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3)
    {PW : Measure ΩW} [IsProbabilityMeasure PW] {W : (Space d → ℝ) → ΩW → ℝ}
    (hW : IsWhiteNoise d W PW) (ν2 : ℝ) (Z : ℝ → Space d → ΩW → ℝ)
    (hmod : ∀ t : ℝ, 0 ≤ t → ∀ x, Z t x =ᵐ[PW] gaussianPotential d ν2 W t x)
    (hc : ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂PW,
      ContinuousOn (fun q : ℝ × Space d => Z q.1 q.2 ω) (Set.Icc 0 T ×ˢ Set.univ))
    {PB : Measure ΩB} [IsProbabilityMeasure PB] {x : Space d} {B : ℝ≥0 → ΩB → Space d}
    (hB : IsBrownian d x B PB) (hBm : ∀ r, StronglyMeasurable (B r))
    (hBc : ∀ b, Continuous fun r => B r b) :
    ∀ᵐ ω ∂PW, ∀ t δ : ℝ≥0,
      Martingale (fun r b => Z (t - min r t + δ : ℝ≥0) (B (min r t) b) ω -
        Z (t - min r t : ℝ≥0) (B (min r t) b) ω) (natFiltration B hBm) PB := by
  have hcont : ∀ᵐ ω ∂PW, Continuous fun q : ℝ≥0 × Space d => Z q.1 q.2 ω := by
    have hh := ae_all_iff.mpr (fun n : ℕ => hc ((n : ℝ) + 1) (by positivity))
    exact hh.mono fun ω hω => continuous_nonnegative_time_of_bounded_strips (fun t x => Z t x ω) hω
  filter_upwards [gaussianPotential_increment_semigroup_common hd hd3 hW ν2 Z hmod hc, hcont] with ω hs hz
  intro t δ
  apply brownian_heat_semigroup_martingale hd hB hBm hBc
    (fun s y => Z (s + δ : ℝ≥0) y ω - Z s y ω) ?_ ?_ t
  · exact (hz.comp ((continuous_fst.add continuous_const).prodMk continuous_snd)).sub hz
  · intro r hr s z
    simpa only [NNReal.coe_add, add_assoc] using hs r s δ hr s.property δ.property z

theorem gaussianPotential_stopped_increment_integral {ΩW ΩB : Type*}
    [MeasurableSpace ΩW] [MeasurableSpace ΩB] {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3)
    {PW : Measure ΩW} [IsProbabilityMeasure PW] {W : (Space d → ℝ) → ΩW → ℝ}
    (hW : IsWhiteNoise d W PW) (ν2 : ℝ) (Z : ℝ → Space d → ΩW → ℝ)
    (hmod : ∀ t : ℝ, 0 ≤ t → ∀ x, Z t x =ᵐ[PW] gaussianPotential d ν2 W t x)
    (hc : ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂PW,
      ContinuousOn (fun q : ℝ × Space d => Z q.1 q.2 ω) (Set.Icc 0 T ×ˢ Set.univ))
    {PB : Measure ΩB} [IsProbabilityMeasure PB] {x : Space d} {B : ℝ≥0 → ΩB → Space d}
    (hB : IsBrownian d x B PB) (hBm : ∀ r, StronglyMeasurable (B r))
    (hBc : ∀ b, Continuous fun r => B r b) :
    ∀ᵐ ω ∂PW, ∀ t δ : ℝ≥0, ∀ τ : ΩB → ℝ≥0,
      IsBrownianStopping B τ → (∀ b, τ b ≤ t) →
      Integrable (fun b => Z (t - τ b + δ : ℝ≥0) (B (τ b) b) ω -
        Z (t - τ b : ℝ≥0) (B (τ b) b) ω) PB ∧
      (∫ b, Z (t - τ b + δ : ℝ≥0) (B (τ b) b) ω -
        Z (t - τ b : ℝ≥0) (B (τ b) b) ω ∂PB) = Z (t + δ) x ω - Z t x ω := by
  have hcont : ∀ᵐ ω ∂PW, Continuous fun q : ℝ≥0 × Space d => Z q.1 q.2 ω := by
    have hh := ae_all_iff.mpr (fun n : ℕ => hc ((n : ℝ) + 1) (by positivity))
    exact hh.mono fun ω hω => continuous_nonnegative_time_of_bounded_strips (fun t x => Z t x ω) hω
  filter_upwards [gaussianPotential_backward_increment_martingale hd hd3 hW ν2 Z hmod hc hB hBm hBc,
    hcont] with ω hm hz
  intro t δ τ hτ hτt
  let M (r : ℝ≥0) (b : ΩB) := Z (t - min r t + δ : ℝ≥0) (B (min r t) b) ω -
    Z (t - min r t : ℝ≥0) (B (min r t) b) ω
  have hMc : ∀ b, Continuous fun r => M r b := by
    intro b
    exact (hz.comp (((continuous_const.sub (continuous_id.min continuous_const)).add continuous_const).prodMk
      ((hBc b).comp (continuous_id.min continuous_const)))).sub
        (hz.comp ((continuous_const.sub (continuous_id.min continuous_const)).prodMk
          ((hBc b).comp (continuous_id.min continuous_const))))
  have hi := integrable_stopped_martingale_eq_of_continuous PB (natFiltration B hBm) M (hm t δ)
    hMc τ ((isBrownianStopping_iff_natFiltration B hBm τ).mp hτ) t hτt
  have he : (fun b => M (τ b) b) = (fun b => Z (t - τ b + δ : ℝ≥0) (B (τ b) b) ω -
      Z (t - τ b : ℝ≥0) (B (τ b) b) ω) := by
    funext b
    simp only [M, min_eq_left (hτt b)]
  rw [← he]
  refine ⟨hi.1, hi.2.trans ?_⟩
  calc
    (∫ b, M 0 b ∂PB) = ∫ _ : ΩB, Z (t + δ) x ω - Z t x ω ∂PB := by
      apply integral_congr_ae
      filter_upwards [hB.start] with b hb
      simp [M, hb]
    _ = Z (t + δ) x ω - Z t x ω := by simp


end Sandpile.Support
