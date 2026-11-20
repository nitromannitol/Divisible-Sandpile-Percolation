import Sandpile.Support.StoppedProcessConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Stopped minima on small events

If the probability that one bounded time precedes another tends to zero, an
integrably dominated continuous process has convergent expectations at their
minima.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

/-- If the event on which `τ n` precedes `σ` has vanishing probability, the
expectation of an integrably dominated continuous process at `min σ (τ n)`
converges to its expectation at `σ`. -/
theorem Sandpile.Support.tendsto_integral_stopped_min_of_small_events
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (M : ℝ≥0 → Ω → ℝ) (hMm : ∀ t, StronglyMeasurable (M t))
    (hMc : ∀ ω, Continuous fun t => M t ω) (T : ℝ≥0)
    (D : Ω → ℝ) (hDi : Integrable D P)
    (hD : ∀ᵐ ω ∂P, ∀ t ≤ T, ‖M t ω‖ ≤ D ω)
    (σ : Ω → ℝ≥0) (hσm : Measurable σ) (hσT : ∀ ω, σ ω ≤ T)
    (τ : ℕ → Ω → ℝ≥0) (hτm : ∀ n, Measurable (τ n))
    (hsmall : Tendsto (fun n => P {ω | τ n ω < σ ω}) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, M (min (σ ω) (τ n ω)) ω ∂P) atTop
      (𝓝 (∫ ω, M (σ ω) ω ∂P)) := by
  let A : ℕ → Set Ω := fun n => {ω | τ n ω < σ ω}
  let C : Ω → ℝ := fun ω => 2 * ‖D ω‖
  have hCi : Integrable C P := hDi.norm.const_mul 2
  have hAtail : Tendsto (fun n => ∫ ω in A n, C ω ∂P) atTop (𝓝 0) :=
    hCi.tendsto_setIntegral_nhds_zero hsmall
  have hjoint : StronglyMeasurable (Function.uncurry M) :=
    stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable hMc hMm
  have hm : ∀ ρ : Ω → ℝ≥0, Measurable ρ →
      AEStronglyMeasurable (fun ω => M (ρ ω) ω) P := fun ρ hρ =>
    (hjoint.comp_measurable (hρ.prodMk measurable_id)).aestronglyMeasurable
  have hi : ∀ ρ : Ω → ℝ≥0, Measurable ρ → (∀ ω, ρ ω ≤ T) →
      Integrable (fun ω => M (ρ ω) ω) P := by
    intro ρ hρ hρT
    exact hDi.mono' (hm ρ hρ) (hD.mono fun ω hω => hω (ρ ω) (hρT ω))
  have hσi := hi σ hσm hσT
  let f : ℕ → Ω → ℝ := fun n ω => M (min (σ ω) (τ n ω)) ω - M (σ ω) ω
  have hfi : ∀ n, Integrable (f n) P := fun n =>
    (hi (fun ω => min (σ ω) (τ n ω)) (hσm.min (hτm n))
      (fun ω => (min_le_left _ _).trans (hσT ω))).sub hσi
  have hbound : ∀ n, ‖∫ ω, f n ω ∂P‖ ≤ ∫ ω in A n, C ω ∂P := by
    intro n
    have heq : (∫ ω, f n ω ∂P) = ∫ ω in A n, f n ω ∂P := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro ω hω
      have hh : σ ω ≤ τ n ω := le_of_not_gt hω
      simp only [f, min_eq_left hh, sub_self]
    rw [heq]
    calc
      _ ≤ ∫ ω in A n, ‖f n ω‖ ∂P := norm_integral_le_integral_norm _
      _ ≤ ∫ ω in A n, C ω ∂P := by
        apply integral_mono_ae (hfi n).norm.integrableOn hCi.integrableOn
        filter_upwards [ae_restrict_of_ae hD] with ω hω
        have h1 := hω (min (σ ω) (τ n ω)) ((min_le_left _ _).trans (hσT ω))
        have h2 := hω (σ ω) (hσT ω)
        dsimp only [f, C]
        have hDle : D ω ≤ ‖D ω‖ := by simpa only [Real.norm_eq_abs] using le_abs_self (D ω)
        linarith [norm_sub_le (M (min (σ ω) (τ n ω)) ω) (M (σ ω) ω)]
  have hnorm : Tendsto (fun n => ‖∫ ω, f n ω ∂P‖) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hAtail
      (fun _ => norm_nonneg _) hbound
  have hf0 : Tendsto (fun n => ∫ ω, f n ω ∂P) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  apply tendsto_sub_nhds_zero_iff.mp
  simpa only [f, integral_sub (hi _ (hσm.min (hτm _))
    (fun ω => (min_le_left _ _).trans (hσT ω))) hσi] using hf0
