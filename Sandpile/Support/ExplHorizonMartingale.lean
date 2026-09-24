/-
Horizon-free Brownian rewards from a backward heat-increment martingale.

For t <= T, the relevant process is
  h(T - min(r,t), B(min(r,t))) - h(t - min(r,t), B(min(r,t))).
Bounded optional sampling identifies its expectation at every admissible stop
with h(T,z) - h(t,z). The individual payoff integrals are legitimate under the
stated common integrable envelope, so this gives HorizonFreeIncrement.

The martingale property is stated explicitly: continuity alone does not imply
it. For a continuous Gaussian heat potential it is the semigroup identity still
needed after stochastic Fubini. The link from IsBrownianStopping to measurable
natural-filtration stopping times is also explicit.
-/
import Sandpile.Support.ExplHorizon
import Sandpile.Support.ExplOptionalSampling

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile.Continuum

open Sandpile.Support

theorem horizonFreeIncrement_of_backward_martingale {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → Space d)
    (hBc : ∀ ω, Continuous fun r => B r ω) (hBm : ∀ r, StronglyMeasurable (B r))
    (h : ℝ → Space d → ℝ) (hc : Continuous fun p : ℝ≥0 × Space d => h p.1 p.2)
    (t T : ℝ≥0) (htT : t ≤ T) (z : Space d) (hstart : ∀ᵐ ω ∂P, B 0 ω = z)
    (𝔽 : Filtration ℝ≥0 mΩ)
    (hclass : ∀ τ : Ω → ℝ≥0, IsBrownianStopping B τ →
      Measurable τ ∧ IsStoppingTime 𝔽 (fun ω => (τ ω : ℝ≥0∞)))
    (hM : Martingale (fun r ω => h (T - min r t : ℝ≥0) (B (min r t) ω) -
      h (t - min r t : ℝ≥0) (B (min r t) ω)) 𝔽 P)
    (D : Ω → ℝ) (hD : Integrable D P)
    (hdom : ∀ᵐ ω ∂P, ∀ r : ℝ≥0, r ≤ t →
      ‖h (T - r : ℝ≥0) (B r ω)‖ ≤ D ω ∧ ‖h (t - r : ℝ≥0) (B r ω)‖ ≤ D ω) :
    HorizonFreeIncrement B P h t T z := by
  intro τ hτ hτt
  have hbt : ∀ ω, τ ω ≤ t := hτt
  obtain ⟨hτm, hτs⟩ := hclass τ hτ
  let M (r : ℝ≥0) (ω : Ω) := h (T - min r t : ℝ≥0) (B (min r t) ω) -
    h (t - min r t : ℝ≥0) (B (min r t) ω)
  have hMc : ∀ ω, Continuous fun r => M r ω := by
    intro ω
    exact (hc.comp ((continuous_const.sub (continuous_id.min continuous_const)).prodMk
      ((hBc ω).comp (continuous_id.min continuous_const)))).sub
        (hc.comp ((continuous_const.sub (continuous_id.min continuous_const)).prodMk
          ((hBc ω).comp (continuous_id.min continuous_const))))
  have hDM : ∀ᵐ ω ∂P, ∀ r : ℝ≥0, r ≤ t + 1 → ‖M r ω‖ ≤ 2 * D ω := by
    filter_upwards [hdom] with ω hω
    intro r _
    exact (norm_sub_le _ _).trans (by linarith [(hω (min r t) (min_le_right _ _)).1,
      (hω (min r t) (min_le_right _ _)).2])
  have hi := integrable_stopped_martingale_and_integral_eq P 𝔽 M hM hMc τ hτs hτm t hbt
    (fun ω => 2 * D ω) (hD.const_mul 2) hDM
  have hj : StronglyMeasurable (Function.uncurry B) :=
    stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable hBc hBm
  have hpos : Measurable (fun ω => B (τ ω) ω) :=
    hj.measurable.comp (hτm.prodMk measurable_id)
  have hI (a : ℝ≥0) (ha : a = t ∨ a = T) :
      Integrable (fun ω => h (a - τ ω : ℝ≥0) (B (τ ω) ω)) P := by
    apply hD.mono' (hc.measurable.comp
      ((measurable_const.sub hτm).prodMk hpos)).aestronglyMeasurable
    filter_upwards [hdom] with ω hω
    rcases ha with rfl | rfl
    · exact (hω (τ ω) (hbt ω)).2
    · exact (hω (τ ω) (hbt ω)).1
  have hz : (∫ ω, M 0 ω ∂P) = h T z - h t z := by
    calc (∫ ω, M 0 ω ∂P) = ∫ _ : Ω, h T z - h t z ∂P := by
          apply integral_congr_ae
          filter_upwards [hstart] with ω hω
          simp [M, hω]
      _ = h T z - h t z := by simp
  have hdiff : (∫ ω, h (T - τ ω : ℝ≥0) (B (τ ω) ω) ∂P) -
      (∫ ω, h (t - τ ω : ℝ≥0) (B (τ ω) ω) ∂P) = h T z - h t z := by
    rw [← integral_sub (hI T (Or.inr rfl)) (hI t (Or.inl rfl))]
    have he : (fun ω => M (τ ω) ω) = fun ω =>
        h (T - τ ω : ℝ≥0) (B (τ ω) ω) - h (t - τ ω : ℝ≥0) (B (τ ω) ω) := by
      funext ω
      simp only [M, min_eq_left (hbt ω)]
    rw [← he]
    exact hi.2.trans hz
  have hsubt (ω : Ω) : ((t - τ ω : ℝ≥0) : ℝ) = (t : ℝ) - τ ω := NNReal.coe_sub (hbt ω)
  have hsubT (ω : Ω) : ((T - τ ω : ℝ≥0) : ℝ) = (T : ℝ) - τ ω :=
    NNReal.coe_sub ((hbt ω).trans htT)
  simp_rw [hsubt, hsubT] at hdiff
  rw [integral_neg, integral_neg]
  linarith

end Sandpile.Continuum
